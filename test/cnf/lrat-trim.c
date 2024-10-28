static const char *version = "0.2.0";

// clang-format off

static const char * usage =

"usage: lrat-trim [ <option> ... ] <file> ...\n"
"\n"
"where '<option> ...' is a potentially empty list of the following options\n"
"\n"
"  -a | --ascii    output proof in ASCII format (default is binary)\n"
"  -f | --force    overwrite CNF alike second file with proof\n"
"  -S | --forward  forward check all added clauses eagerly\n"
"  -h | --help     print this command line option summary\n"
#ifdef LOGGING
"  -l | --log      print all messages including logging messages\n"
#endif
"  -q | --quiet    be quiet and do not print any messages\n" 
"  -s | --strict   expect strict resolution chain format\n"
"  -t | --track    track more detailed addition and deletion information\n"
"  -v | --verbose  enable verbose messages\n"
"  -V | --version  print version only\n"
"\n"
"  --no-binary     synonym to '-a' or '--ascii'\n"
"  --no-check      disable checking clauses (default without CNF)\n"
"  --no-trim       disable trimming (assume all clauses used)\n"
"\n"
"  --relax         ignore deletion of clauses which were never added\n"
"\n"
"and '<file> ...' is a non-empty list of at most four DIMACS and LRAT files:\n"
"\n"
"  <input-proof>\n"
"  <input-cnf> <input-proof>\n"
"\n"
"  <input-proof> <output-proof>\n"
"  <input-cnf> <input-proof> <output-proof>\n"
"  <input-cnf> <input-proof> <output-proof> <output-cnf>\n"
"\n"

"The required input proof in LRAT format is parsed and trimmed and\n"
"optionally written to the output proof file if it is specified.  Otherwise\n"
"the proof is trimmed only in memory producing trimming statistics.\n"
"\n"
"If an input CNF is also specified then it is assumed to be in DIMACS format\n"
"and parsed before reading the LRAT proof.  Providing a CNF triggers to\n"
"check and not only trim a proof.  If checking fails an error message is\n"
"produced and the program aborts with exit code '1'.  If checking succeeds\n"
"the exit code is '0', if no empty clause was derived. Otherwise if the CNF\n"
"or proof contains an empty clause and checking succeeds, then the exit\n"
"code is '20', i.e., the same exit code as for unsatisfiable formulas in\n"
"the SAT competition.  In this case 's VERIFIED' is printed too.\n"
"\n"
"The status of clauses, i.e., whether they are added or have been deleted\n"
"is always tracked and checked precisely.  It is considered an error if\n"
"a clause is used in a proof line which was deleted before.  In order to\n"
"determine in which proof line exactly the offending clause was deleted\n"
"the user can additionally specify '--track' to track this information,\n"
"which can then give a more informative error message.\n"
"\n"
"If the CNF or the proof contains an empty clause, proof checking is by\n"
"default restricted to the trimmed proof.  Without empty clause, neither\n"
"in the CNF nor in the proof, trimming is skipped.  The same effect can\n"
"be achieved by using '--no-trim', which has the additional benefit to\n"
"enforce forward on-the-fly checking while parsing the proof. This mode\n"
"allows to delete clauses eagerly and gives the chance to reduce memory\n"
"usage substantially.\n"
"\n"
"At most one of the input path names can be '-' which leads to reading\n"
"the corresponding input from '<stdin>'.  Similarly using '-' for one\n"
"of the output files writes to '<stdout>'.  When exactly two files are\n"
"given the first file is opened and read first and to determine its format\n"
"(LRAT or DIMACS) by checking the first read character ('p' or 'c' gives\n"
"DIMACS format).  The result also determines the type of the second file\n"
"as either proof output or as proof input.  Two files can not have the\n"
"same specified file path except for '-' and '/dev/null'.  The latter is a\n"
"hard-coded name and will not actually be opened nor written to '/dev/null'\n"
"(whether it exists or not on the system).\n"

;

// clang-format on

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct file {
  const char *path;
  FILE *file;
  size_t bytes;
  size_t lines;
  bool binary;
  char close;
  bool eof;
  int last;
  int saved;
};

struct bool_stack {
  bool *begin, *end, *allocated;
};

struct int_stack {
  int *begin, *end, *allocated;
};

struct char_map {
  signed char *begin, *end;
};

struct int_map {
  int *begin, *end;
};

struct ints_map {
  int **begin, **end;
};

struct size_t_map {
  size_t *begin, *end;
};

struct statistics {
  struct {
    struct {
      size_t added, deleted;
    } cnf, proof;
  } original, trimmed;
  struct {
    struct {
      size_t total;
      size_t empty;
    } checked;
    size_t resolved;
  } clauses;
  struct {
    size_t assigned;
    size_t marked;
  } literals;
} statistics;

// At-most three files set up during option parsing.

static struct file files[4];
static size_t size_files;

// Current input and output file for writing and reading functions.

// As we only work on one input sequentially during 'parse_proof' or
// before optionally in 'parse_cnf' we keep the current 'input' file as
// static global data structures which helps the compiler to optimize
// 'read_buffer' and 'read_char' as well code into which theses are inlined.
// In particular see the discussion below on 'faster_than_default_isdigit'.

// A similar argument applies to the 'output' file.

static struct file input, output;

struct {
  struct file *input, *output;
} cnf, proof;

static const char *ascii;
static const char *force;
static const char *forward;
static const char *nocheck;
static const char *notrim;
static const char *strict;
static const char *track;
static int verbosity;

static bool checking;
static bool trimming;
static bool relax;

static int empty_clause;
static int last_clause_added_in_cnf;
static int first_clause_added_in_proof;

static struct {
  struct char_map marks;
  struct char_map values;
  int original;
} variables;

static struct int_stack trail;

static struct {
  struct char_map status;
  struct ints_map literals;
  struct ints_map antecedents;
  struct size_t_map deleted;
  struct size_t_map added;
  struct int_map referenced;
  struct int_map heads;
  struct int_map links;
  struct int_map used;
  struct int_map map;
} clauses;

static void die (const char *, ...) __attribute__ ((format (printf, 1, 2)));
static void prr (const char *, ...) __attribute__ ((format (printf, 1, 2)));
static void msg (const char *, ...) __attribute__ ((format (printf, 1, 2)));
static void vrb (const char *, ...) __attribute__ ((format (printf, 1, 2)));
static void wrn (const char *, ...) __attribute__ ((format (printf, 1, 2)));

static void die (const char *fmt, ...) {
  fputs ("lrat-trim: error: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void prr (const char *fmt, ...) {
  assert (input.path);
  if (input.binary) {
    fprintf (stderr,
             "lrat-trim: parse error in '%s' after reading %zu bytes: ",
             input.path, input.bytes);
  } else {
    size_t line = input.lines + 1;
    if (input.last == '\n')
      line--;
    fprintf (stderr,
             "lrat-trim: parse error in '%s' %s line %zu: ", input.path,
             input.eof && input.last == '\n' ? "after" : "in", line);
  }
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void msg (const char *fmt, ...) {
  if (verbosity < 0)
    return;
  fputs ("c ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void vrb (const char *fmt, ...) {
  if (verbosity < 1)
    return;
  fputs ("c ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void wrn (const char *fmt, ...) {
  if (verbosity < 0)
    return;
  fputs ("c WARNING ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

#define size_pretty_buffer 256
#define num_pretty_buffers 2

static char pretty_buffer[num_pretty_buffers][size_pretty_buffer];
static int current_pretty_buffer;

static char *next_pretty_buffer () {
  char *res = pretty_buffer[current_pretty_buffer++];
  if (current_pretty_buffer == num_pretty_buffers)
    current_pretty_buffer = 0;
  return res;
}

static const char *pretty_bytes (size_t bytes) {
  char *buffer = next_pretty_buffer ();
  double kb = bytes / (double) (1u << 10);
  double mb = bytes / (double) (1u << 20);
  double gb = bytes / (double) (1u << 30);
  if (kb < 1)
    snprintf (buffer, size_pretty_buffer, "%zu bytes", bytes);
  else if (mb < 1)
    snprintf (buffer, size_pretty_buffer, "%zu bytes %.1f KB", bytes, kb);
  else if (gb < 1)
    snprintf (buffer, size_pretty_buffer, "%zu bytes %.1f MB", bytes, mb);
  else
    snprintf (buffer, size_pretty_buffer, "%zu bytes %.1f GB", bytes, gb);
  assert (strlen (buffer) < size_pretty_buffer);
  return buffer;
}

#ifdef COVERAGE

// This part of the code enclosed with '#ifdef COVERAGE' is only useful
// during testing and debugging and should not be used in production by
// keeping 'COVERAGE' undefined.

// The motivation for having this is that 'lrat-trim' is meant to be robust
// in terms of producing error messages if it runs out-of-memory and not
// just give a segmentation fault if it does.

// In order to test 'out-of-memory' errors and produce coverage we replace
// the standard allocation functions with dedicated allocators which fail
// after a given number of allocated bytes specified through the environment
// variable 'LRAT_TRIM_ALLOCATION_LIMIT'.

#define size_allocation_lines ((size_t) (1u << 12))

static size_t allocation_lines[size_allocation_lines];
static bool allocation_limit_set;
static size_t allocation_limit;
static size_t allocated_bytes;

static bool check_allocation (size_t line, size_t bytes) {
  assert (bytes);
  if (!allocation_limit_set) {
    const char *env = getenv ("LRAT_TRIM_ALLOCATION_LIMIT");
    allocation_limit = env ? atol (env) : ~(size_t) 0;
    printf ("c COVERED allocated bytes limit %zu\n", allocation_limit);
    allocation_limit_set = true;
  }
  assert (line < size_allocation_lines);
  if (!allocation_lines[line])
    printf ("c COVERED allocation at line %zu after allocating %zu bytes\n",
            line, allocated_bytes);
#ifdef LOGGING
  if (verbosity == INT_MAX)
    printf ("c COVERED allocating %zu bytes at line %zu\n", bytes, line);
#endif
  allocation_lines[line] += bytes;
  allocated_bytes += bytes;
  return allocated_bytes <= allocation_limit;
}

static void *coverage_malloc (size_t line, size_t bytes) {
  return check_allocation (line, bytes) ? malloc (bytes) : 0;
}

static void *coverage_calloc (size_t line, size_t n, size_t bytes) {
  return check_allocation (line, n * bytes) ? calloc (n, bytes) : 0;
}

static void *coverage_realloc (size_t line, void *p, size_t bytes) {
  return check_allocation (line, bytes) ? realloc (p, bytes) : 0;
}

#define malloc(BYTES) coverage_malloc (__LINE__, BYTES)
#define calloc(N, BYTES) coverage_calloc (__LINE__, N, BYTES)
#define realloc(P, BYTES) coverage_realloc (__LINE__, P, BYTES)

#endif

#define ZERO(E) \
  do { \
    memset (&(E), 0, sizeof (E)); \
  } while (0)

#define SIZE(STACK) ((STACK).end - (STACK).begin)
#define CAPACITY(STACK) ((STACK).allocated - (STACK).begin)

#define EMPTY(STACK) ((STACK).end == (STACK).begin)
#define FULL(STACK) ((STACK).end == (STACK).allocated)

#define ENLARGE(STACK) \
  do { \
    size_t OLD_CAPACITY = SIZE (STACK); \
    size_t NEW_CAPACITY = OLD_CAPACITY ? 2 * OLD_CAPACITY : 1; \
    size_t NEW_BYTES = NEW_CAPACITY * sizeof *(STACK).begin; \
    if (!((STACK).begin = realloc ((STACK).begin, NEW_BYTES))) \
      die ("out-of-memory enlarging '" #STACK "' stack"); \
    (STACK).end = (STACK).begin + OLD_CAPACITY; \
    (STACK).allocated = (STACK).begin + NEW_CAPACITY; \
  } while (0)

#define PUSH(STACK, DATA) \
  do { \
    if (FULL (STACK)) \
      ENLARGE (STACK); \
    *(STACK).end++ = (DATA); \
  } while (0)

#define ACCESS(STACK, OFFSET) \
  ((STACK).begin[assert ((OFFSET) < SIZE (STACK)), (OFFSET)])

#define POP(STACK) (assert (!EMPTY (STACK)), *--(STACK).end)

#define CLEAR(STACK) \
  do { \
    (STACK).end = (STACK).begin; \
  } while (0)

#define RELEASE(STACK) free ((STACK).begin)

#define ADJUST(MAP, N) \
  do { \
    size_t NEEDED_SIZE = (size_t) (N) + 1; \
    size_t OLD_SIZE = SIZE (MAP); \
    if (OLD_SIZE >= NEEDED_SIZE) \
      break; \
    size_t NEW_SIZE = OLD_SIZE ? 2 * OLD_SIZE : 1; \
    void *OLD_BEGIN = (MAP).begin; \
    void *NEW_BEGIN; \
    while (NEW_SIZE < NEEDED_SIZE) \
      NEW_SIZE *= 2; \
    if (OLD_SIZE) { \
      size_t NEW_BYTES = NEW_SIZE * sizeof *(MAP).begin; \
      assert (OLD_BEGIN); \
      NEW_BEGIN = realloc (OLD_BEGIN, NEW_BYTES); \
      if (!NEW_BEGIN) \
        die ("out-of-memory resizing '" #MAP "' map"); \
      size_t OLD_BYTES = OLD_SIZE * sizeof *(MAP).begin; \
      size_t DELTA_BYTES = NEW_BYTES - OLD_BYTES; \
      memset ((char *) NEW_BEGIN + OLD_BYTES, 0, DELTA_BYTES); \
    } else { \
      assert (!OLD_BEGIN); \
      NEW_BEGIN = calloc (NEW_SIZE, sizeof *(MAP).begin); \
      if (!NEW_BEGIN) \
        die ("out-of-memory initializing '" #MAP "' map"); \
    } \
    (MAP).begin = NEW_BEGIN; \
    (MAP).end = (MAP).begin + NEW_SIZE; \
  } while (0)

#ifndef NDEBUG

static void release_ints_map (struct ints_map *map) {
  int **begin = map->begin;
  int **end = map->end;
  for (int **p = begin; p != end; p++)
    if (*p)
      free (*p);
  free (begin);
}

#endif

#ifdef LOGGING

static bool logging () { return verbosity == INT_MAX; }

static void logging_prefix (const char *, ...)
    __attribute__ ((format (printf, 1, 2)));

static void logging_prefix (const char *fmt, ...) {
  assert (logging ());
  fputs ("c LOGGING ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
}

static void logging_suffix () {
  assert (logging ());
  fputc ('\n', stdout);
  fflush (stdout);
}

#define dbg(...) \
  do { \
    if (!logging ()) \
      break; \
    logging_prefix (__VA_ARGS__); \
    logging_suffix (); \
  } while (0)

#define dbgs(INTS, ...) \
  do { \
    if (!logging ()) \
      break; \
    logging_prefix (__VA_ARGS__); \
    const int *P = (INTS); \
    while (*P) \
      printf (" %d", *P++); \
    logging_suffix (); \
  } while (0)

#else

#define dbg(...) \
  do { \
  } while (0)

#define dbgs(...) \
  do { \
  } while (0)

#endif

// Having a statically allocated read buffer allows to inline more character
// reading code into integer parsing routines and thus speed up overall
// parsing time substantially (saw 30% improvement).

#define size_buffer (1u << 20)

struct buffer {
  unsigned char chars[size_buffer];
  size_t pos, end;
} buffer;

static size_t fill_buffer () {
  assert (input.file);
  buffer.pos = 0;
  buffer.end = fread (buffer.chars, 1, size_buffer, input.file);
  return buffer.end;
}

// These three functions were not inlined with gcc-11 but should be despite
// having declared them as 'inline' and thus we use this 'always_inline'
// attribute which seems to succeed to force inlining.  Having them inlined
// really gives a performance boost.

static inline int read_buffer (void) __attribute__ ((always_inline));

static inline void count_ascii (int ch) __attribute__ ((always_inline));
static inline int read_ascii (void) __attribute__ ((always_inline));

static inline void count_binary (int ch) __attribute__ ((always_inline));
static inline int read_binary (void) __attribute__ ((always_inline));

static inline int read_buffer (void) {
  if (buffer.pos == buffer.end && !fill_buffer ())
    return EOF;
  return buffer.chars[buffer.pos++];
}

static inline void count_ascii (int ch) {
  if (ch == '\n')
    input.lines++;
  if (ch != EOF) {
    input.bytes++;
    input.last = ch;
  }
}

static inline int read_ascii (void) {
  assert (input.file);
  assert (!input.binary);
  assert (input.saved == EOF);
  int res = read_buffer ();
  if (res == EOF)
    input.eof = true;
  if (res == '\r') {
    count_ascii (res);
    res = read_buffer ();
    if (res == EOF)
      input.eof = true;
    if (res != '\n')
      prr ("carriage-return without following new-line");
  }
  count_ascii (res);
  return res;
}

// To skip 'c', 's' and 'v' lines in case the proof is interleaved with the
// standard output of a SAT solver use this function.  We have a similar
// function below in 'open_input_files' but there we actually really skip
// the start of the input file and only save the first character of a
// non-comment character.  Here we have to be careful with statistics too
// and also can not use 'read_ascii' or 'read_binary' as this function is
// shared between ASCII and binary mode.

static inline void read_until_new_line (void) {
  assert (input.file);
  assert (input.saved == EOF);
  int ch;
  while ((ch = read_buffer ()) != '\n') {
    if (ch == EOF)
      prr ("unexpected end-of-file before new-line");
    input.bytes++;
    if (ch == '\r') {
      ch = getc (input.file);
      if (ch != EOF)
        input.bytes++;
      if (ch == '\n')
        break;
      prr ("carriage-return without following new-line");
    }
  }
  if (!input.binary)
    input.lines++;
}

static inline void count_binary (int ch) {
  if (ch != EOF)
    input.bytes++;
}

static inline int read_binary (void) {
  assert (input.file);
  assert (input.binary);
  assert (input.saved == EOF);
  int res = read_buffer ();
  count_binary (res);
  return res;
}

// We only need a look-ahead for the very first byte to determined whether
// the first input file is a DIMACS file or not (if exactly two files are
// specified).  In both cases we save this very first character as 'saved'
// in the input file and then when coming back to parsing this file
// will give back this saved character as first read character.

// Note that statistics of the file are adjusted during reading the
// saved character the first time do not need to be updated here again.

// Originally we simply only had one 'read_char' function, but factoring out
// this rare situation and restricting it to the beginning of parsing helped
// the compiler to produce better code for the hot-stop which merges the
// code of the inlined 'read_char' and 'isdigit'.

static int read_first_char (void) {
  if (!input.file)
    return EOF;
  int res = input.saved;
  if (res == EOF)
    res = read_ascii ();
  else
    input.saved = EOF;
  return res;
}

static void flush_buffer () {
  size_t bytes = buffer.pos;
  if (!bytes)
    return;
  if (!output.file) {
    buffer.pos = 0;
    return;
  }
  size_t written = fwrite (buffer.chars, 1, bytes, output.file);
  bool failed = (written != bytes);
#ifdef COVERAGE
  if (getenv ("LRAT_TRIM_FAKE_FRWRITE_FAILURE"))
    failed = true;
#endif
  if (failed) {
    assert (output.path);
    die ("flushing %zu bytes of write-buffer to '%s' failed", bytes,
         output.path);
  }
  buffer.pos = 0;
}

static inline void write_binary (unsigned char)
    __attribute__ ((always_inline));

static inline void write_unsigned (unsigned)
    __attribute__ ((always_inline));

static inline void write_signed (int) __attribute__ ((always_inline));

static inline void write_binary (unsigned char ch) {
  if (buffer.pos == size_buffer)
    flush_buffer ();
  buffer.chars[buffer.pos++] = ch;
  output.bytes++;
}

static inline void write_unsigned (unsigned u) {
  while (u > 127) {
    write_binary (128 | (u & 127));
    u >>= 7;
  }
  write_binary (u);
}

static inline void write_signed (int i) {
  assert (i != INT_MIN);
  write_unsigned ((i < 0) + 2 * (unsigned) abs (i));
}

static inline void write_ascii (unsigned char)
    __attribute__ ((always_inline));

static inline void write_ascii (unsigned char ch) {
  if (buffer.pos == size_buffer)
    flush_buffer ();
  buffer.chars[buffer.pos++] = ch;
  output.bytes++;
  if (ch == '\n')
    output.lines++;
}

static inline void write_space () { write_ascii (' '); }

static inline void write_str (const char *str) {
  for (const char *p = str; *p; p++)
    write_ascii (*p);
}

static inline void write_int (int i) __attribute__ ((always_inline));

static char int_buffer[16];

static inline void write_int (int i) {
  if (i) {
    char *p = int_buffer + sizeof int_buffer - 1;
    assert (!*p);
    assert (i != INT_MIN);
    unsigned tmp = abs (i);
    while (tmp) {
      *--p = '0' + (tmp % 10);
      tmp /= 10;
    }
    if (i < 0)
      *--p = '-';
    write_str (p);
  } else
    write_ascii ('0');
}

static char size_t_buffer[32];

static inline void write_size_t (size_t i) {
  if (i) {
    char *p = size_t_buffer + sizeof size_t_buffer - 1;
    assert (!*p);
    size_t tmp = i;
    while (tmp) {
      *--p = '0' + (tmp % 10);
      tmp /= 10;
    }
    write_str (p);
  } else
    write_ascii ('0');
}

#include <sys/resource.h>
#include <sys/time.h>
#include <unistd.h>

static double process_time () {
  struct rusage u;
  double res;
  (void) getrusage (RUSAGE_SELF, &u);
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

static size_t maximum_resident_set_size (void) {
  struct rusage u;
  (void) getrusage (RUSAGE_SELF, &u);
  return ((size_t) u.ru_maxrss) << 10;
}

static double mega_bytes (void) {
  return maximum_resident_set_size () / (double) (1 << 20);
}

static double average (double a, double b) { return b ? a / b : 0; }
static double percent (double a, double b) { return average (100 * a, b); }

static inline void assign_literal (int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  dbg ("assigning literal %d", lit);
  int idx = abs (lit);
  signed char value = lit < 0 ? -1 : 1;
  signed char *v = &ACCESS (variables.values, idx);
  assert (!*v);
  *v = value;
  PUSH (trail, lit);
  statistics.literals.assigned++;
}

static inline void unassign_literal (int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  dbg ("unassigning literal %d", lit);
  int idx = abs (lit);
  signed char *v = &ACCESS (variables.values, idx);
#ifndef NDEBUG
  signed char value = lit < 0 ? -1 : 1;
  assert (*v == value);
#endif
  *v = 0;
}

static void backtrack () {
  for (int *t = trail.begin; t != trail.end; t++)
    unassign_literal (*t);
  CLEAR (trail);
}

static inline signed char assigned_literal (int)
    __attribute ((always_inline));

static inline signed char assigned_literal (int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  int idx = abs (lit);
  signed char res = ACCESS (variables.values, idx);
  if (lit < 0)
    res = -res;
  return res;
}

static void crr (int, const char *, ...)
    __attribute__ ((format (printf, 2, 3)));

static void crr (int id, const char *fmt, ...) {
  fputs ("lrat-trim: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fprintf (stderr, " while checking clause '%d'", id);
  if (track) {
    size_t *addition = &ACCESS (clauses.added, id);
    fprintf (stderr, " at line '%zu' ", *addition);
    assert (proof.input);
    assert (proof.input->path);
    fprintf (stderr, "in '%s'", proof.input->path);
    if (verbosity <= 0)
      fputs (" (use '-v' to print clause)", stderr);
  } else if (verbosity > 0)
    fputs (" (run with '-t' to track line information)", stderr);
  else
    fputs (" (run with '-t' to track line information and "
           "'-v' to print the actual clause)",
           stderr);
  if (verbosity > 0) {
    fputs (": ", stderr);
    int *l = ACCESS (clauses.literals, id);
    while (*l)
      fprintf (stderr, "%d ", *l++);
    fputc ('0', stderr);
  }
  fputc ('\n', stderr);
  exit (1);
}

static void check_clause_non_strictly_by_propagation (int id, int *literals,
                                                      int *antecedents) {
  assert (!strict);
  assert (EMPTY (trail));

  statistics.clauses.resolved++;
  for (int *l = literals, lit; (lit = *l); l++) {
    signed char value = assigned_literal (lit);
    if (value < 0) {
      dbg ("skipping duplicated literal '%d' in clause '%d'", lit, id);
      continue;
    }
    if (value > 0) {
      dbg ("skipping tautological literal '%d' and '%d' "
           "in clause '%d'",
           -lit, lit, id);
    CHECKED:
      backtrack ();
      return;
    }
    assign_literal (-lit);
  }

  for (int *a = antecedents, aid; (aid = *a); a++) {
    if (aid < 0)
      crr (id, "checking negative RAT antecedent '%d' not supported", aid);
    int *als = ACCESS (clauses.literals, aid);
    dbgs (als, "resolving antecedent %d clause", aid);
    statistics.clauses.resolved++;
    int unit = 0;
    for (int *l = als, lit; (lit = *l); l++) {
      signed char value = assigned_literal (lit);
      if (value < 0)
        continue;
      if (unit && unit != lit)
        crr (id, "antecedent '%d' does not produce unit", aid);
      unit = lit;
      if (!value)
        assign_literal (lit);
    }
    if (!unit) {
      dbgs (als,
            "conflicting antecedent '%d' thus checking "
            " of clause '%d' succeeded",
            aid, id);
      goto CHECKED;
    }
  }
  crr (id, "propagating antecedents does not yield conflict");
}

static void check_clause_strictly_by_resolution (int id, int *literals,
                                                 int *antecedents) {
  assert (strict);
  assert (EMPTY (trail));

  int *a = antecedents, aid;
  while ((aid = *a))
    if (aid < 0)
      crr (id, "checking negative RAT antecedent '%d' not supported", aid);
    else
      a++;

  size_t resolvent_size = 0;
  bool first = true;
  while (a != antecedents) {
    aid = *--a;
    int *als = ACCESS (clauses.literals, aid);
    dbgs (als, "resolving antecedent %d clause", aid);
    statistics.clauses.resolved++;
    int unit = 0;
    for (int *l = als, lit; (lit = *l); l++) {
      assert (lit != INT_MIN);
      int idx = abs (lit);
      signed char *m = &ACCESS (variables.marks, idx);
      signed char mark = *m;
      if (!mark) {
        dbg ("marking antecedent literal '%d'", lit);
        *m = lit < 0 ? -1 : 1;
        resolvent_size++;
        continue;
      }
      if (lit < 0)
        mark = -mark;
      if (mark > 0)
        continue;
      assert (mark < 0);
      if (unit)
        crr (id, "multiple pivots '%d' and '%d' in antecedent '%d'", unit,
             lit, aid);
      unit = lit;
    }
    if (first) {
      if (unit)
        crr (id, "multiple pivots '%d' and '%d' in antecedent '%d'", -unit,
             unit, aid);
      first = false;
    } else if (!unit)
      crr (id, "no pivot in antecedent '%d'", aid);
    else {
      dbg ("resolving over pivot literal %d", unit);
      assert (resolvent_size > 0);
      resolvent_size--;
      assert (unit != INT_MIN);
      int idx = abs (unit);
      signed char *m = &ACCESS (variables.marks, idx);
      *m = 0;
    }
  }

  for (int *l = literals, lit; (lit = *l); l++) {
    assert (lit != INT_MIN);
    int idx = abs (lit);
    signed char *m = &ACCESS (variables.marks, idx);
    signed char mark = *m;
    if (!mark)
      crr (id, "literal '%d' not in resolvent", lit);
    if (lit < 0)
      mark = -mark;
    if (mark < 0)
      crr (id, "literal '%d' negated in resolvent", lit);
    *m = 0;
    assert (resolvent_size);
    resolvent_size--;
  }

  if (resolvent_size == 1)
    crr (id, "final resolvent has one additional literal");
  else if (resolvent_size)
    crr (id, "final resolvent has %zu additional literals", resolvent_size);
}

static void check_clause (int id, int *literals, int *antecedents) {
  statistics.clauses.checked.total++;
  if (!*literals)
    statistics.clauses.checked.empty++;
  if (strict)
    check_clause_strictly_by_resolution (id, literals, antecedents);
  else
    check_clause_non_strictly_by_propagation (id, literals, antecedents);
}

static inline bool is_original_clause (int id) {
  int abs_id = abs (id);
  return !abs_id || !first_clause_added_in_proof ||
         abs_id < first_clause_added_in_proof;
}

// Apparently the hot-spot of the parser is checking the loop condition for
// integer parsing which reads the next character from an input file and
// then asks 'isdigit' whether the integer parsed at this point should be
// extended by another digit or the first character (space or new-line)
// after the integer has been reached.  It seems that the claimed fast
// 'isdigit' from 'libc', which we assume is implemented by a table look-up,
// prevents some local compiler optimization as soon the character reading
// code is also inlined (which even for 'getc_unlocked' happened).

// Using the good old range based checked (assuming an ASCII encoding) seems
// to help the compiler to produce better code (around 5% faster).

// We use 'ISDIGIT' instead of 'isdigit' as the later can itself be a macro.

#define ISDIGIT faster_than_default_isdigit

static inline bool faster_than_default_isdigit (int)
    __attribute__ ((always_inline));

static inline bool faster_than_default_isdigit (int ch) {
  return '0' <= ch && ch <= '9';
}

// If the user does have huge integers (larger than 'INT_MAX') in proofs we
// still want to print those integers in the triggered error message.  This
// function takes the integer 'n' parsed so far and the digit 'ch'
// triggering the overflow as argument and then continues reading digits
// from the input file (for a while) and prints the complete parsed integer
// string to a statically allocated buffer which is returned.

static const char *exceeds_int_max (int n, int ch) {
  static char buffer[32];
  const size_t size = sizeof buffer - 5;
  assert (ISDIGIT (ch));
  snprintf (buffer, sizeof buffer, "%d", n);
  size_t i = strlen (buffer);
  do {
    assert (i < sizeof buffer);
    buffer[i++] = ch;
  } while (i < size && ISDIGIT (ch = read_ascii ()));
  if (ch == '\n') {
    assert (input.lines);
    input.lines--;
  }
  if (i == size) {
    assert (i + 3 < sizeof buffer);
    buffer[i++] = '.';
    buffer[i++] = '.';
    buffer[i++] = '.';
  }
  assert (i < sizeof buffer);
  buffer[i] = 0;
  return buffer;
}

static void parse_cnf () {
  if (!cnf.input)
    return;
  double start = process_time ();
  vrb ("starting parsing CNF after %.2f seconds", start);
  input = *cnf.input;
  msg ("reading CNF from '%s'", input.path);
  int ch;
  for (ch = read_first_char (); ch != 'p'; ch = read_ascii ())
    if (ch != 'c')
      prr ("expected 'c' or 'p' as first character");
    else
      while ((ch = read_ascii ()) != '\n')
        if (ch == EOF)
          prr ("end-of-file in comment before header");
  if (read_ascii () != ' ')
    prr ("expected space after 'p'");
  if (read_ascii () != 'c' || read_ascii () != 'n' || read_ascii () != 'f')
    prr ("expected 'p cnf'");
  if (read_ascii () != ' ')
    prr ("expected space after 'p cnf'");
  ch = read_ascii ();
  if (!ISDIGIT (ch))
    prr ("expected digit after 'p cnf '");
  int header_variables = ch - '0';
  while (ISDIGIT (ch = read_ascii ())) {
    if (INT_MAX / 10 < header_variables)
    NUMBER_OF_VARIABLES_EXCEEDS_INT_MAX:
      prr ("number of variables '%s' exceeds 'INT_MAX'",
           exceeds_int_max (header_variables, ch));
    header_variables *= 10;
    int digit = ch - '0';
    if (INT_MAX - digit < header_variables) {
      header_variables /= 10;
      goto NUMBER_OF_VARIABLES_EXCEEDS_INT_MAX;
    }
    header_variables += digit;
  }
  if (ch != ' ')
    prr ("expected space after 'p cnf %d", header_variables);
  ch = read_ascii ();
  if (!ISDIGIT (ch))
    prr ("expected digit after 'p cnf %d '", header_variables);
  int header_clauses = ch - '0';
  while (ISDIGIT (ch = read_ascii ())) {
    if (INT_MAX / 10 < header_clauses)
    NUMBER_OF_CLAUSES_EXCEEDS_INT_MAX:
      prr ("number of clauses '%s' exceeds 'INT_MAX'",
           exceeds_int_max (header_clauses, ch));
    header_clauses *= 10;
    int digit = ch - '0';
    if (INT_MAX - digit < header_clauses) {
      header_clauses /= 10;
      goto NUMBER_OF_CLAUSES_EXCEEDS_INT_MAX;
    }
    header_clauses += digit;
  }
  while (ch == ' ')
    ch = read_ascii ();
  if (ch != '\n')
    prr ("expected new-line after 'p cnf %d %d'", header_variables,
         header_clauses);
  msg ("found 'p cnf %d %d' header", header_variables, header_clauses);
  if (strict)
    ADJUST (variables.marks, header_variables);
  else
    ADJUST (variables.values, header_variables);
  ADJUST (clauses.literals, header_clauses);
  ADJUST (clauses.status, header_clauses);
  int lit = 0, parsed_clauses = 0;
  struct int_stack parsed_literals;
  ZERO (parsed_literals);
  for (;;) {
    ch = read_ascii ();
    if (ch == ' ' || ch == '\t' || ch == '\n')
      continue;
    if (ch == EOF) {
      assert (input.eof);
      if (lit)
        prr ("'0' missing after clause before end-of-file");
      if (parsed_clauses < header_clauses) {
        if (parsed_clauses + 1 == header_clauses)
          prr ("clause missing");
        else
          prr ("%d clauses missing", header_clauses - parsed_clauses);
      }
      break;
    }
    if (ch == 'c') {
    SKIP_COMMENT_AFTER_HEADER:
      while ((ch = read_ascii ()) != '\n')
        if (ch == EOF)
          prr ("end-of-file in comment after header");
      continue;
    }
    int sign;
    if (ch == '-') {
      ch = read_ascii ();
      if (!ISDIGIT (ch))
        prr ("expected digit after '-'");
      if (ch == '0')
        prr ("expected non-zero digit after '-'");
      sign = -1;
    } else {
      if (!ISDIGIT (ch))
        prr ("unexpected character instead of literal");
      sign = 1;
    }
    int idx = ch - '0';
    while (ISDIGIT (ch = read_ascii ())) {
      if (!idx)
        prr ("unexpected digit '%c' after '0'", ch);
      if (INT_MAX / 10 < idx)
      VARIABLE_EXCEEDS_INT_MAX:
        prr ("variable '%s' exceeds 'INT_MAX'", exceeds_int_max (idx, ch));
      idx *= 10;
      int digit = ch - '0';
      if (INT_MAX - digit < idx) {
        idx /= 10;
        goto VARIABLE_EXCEEDS_INT_MAX;
      }
      idx += digit;
    }
    lit = sign * idx;
    if (idx > header_variables)
      prr ("literal '%d' exceeds maximum variable '%d'", lit,
           header_variables);
    if (ch != 'c' && ch != ' ' && ch != '\t' && ch != '\n')
      prr ("expected white space after '%d'", lit);
    if (parsed_clauses >= header_clauses)
      prr ("too many clauses");
    PUSH (parsed_literals, lit);
    if (!lit) {
      parsed_clauses++;
      statistics.original.cnf.added++;
      dbgs (parsed_literals.begin, "clause %d parsed", parsed_clauses);
      size_t size_literals = SIZE (parsed_literals);
      size_t bytes_literals = size_literals * sizeof (int);
      int *l = malloc (bytes_literals);
      if (!l) {
        assert (size_literals);
        die ("out-of-memory allocating literals of size %zu clause %d",
             size_literals - 1, parsed_clauses);
      }
      memcpy (l, parsed_literals.begin, bytes_literals);
      assert (parsed_clauses < SIZE (clauses.literals));
      clauses.literals.begin[parsed_clauses] = l;
      CLEAR (parsed_literals);
      assert (parsed_clauses < SIZE (clauses.status));
      clauses.status.begin[parsed_clauses] = 1;
      if (size_literals == 1 && !empty_clause) {
        vrb ("found empty original clause %d", parsed_clauses);
        statistics.clauses.checked.empty++;
        empty_clause = parsed_clauses;
      }
    }
    if (ch == 'c')
      goto SKIP_COMMENT_AFTER_HEADER;
  }
  assert (parsed_clauses == header_clauses);
  assert (EMPTY (parsed_literals));
  RELEASE (parsed_literals);

  if (input.close)
    fclose (input.file);
  *cnf.input = input;

  vrb ("read %zu CNF lines with %s", input.lines,
       pretty_bytes (input.bytes));

  last_clause_added_in_cnf = parsed_clauses;
  msg ("parsed CNF with %zu added clauses", statistics.original.cnf.added);

  double end = process_time (), duration = end - start;
  vrb ("finished parsing CNF after %.2f seconds", end);
  msg ("parsing original CNF took %.2f seconds and needed %.0f MB memory",
       duration, mega_bytes ());

  variables.original = header_variables;
}

static size_t ignored_deletions = 0;
static struct int_stack parsed_literals;
static struct int_stack parsed_antecedents;

static void delete_antecedent (int other, bool binary, size_t info) {
  if (!first_clause_added_in_proof)
    ADJUST (clauses.status, other);

  signed char *status_ptr = &ACCESS (clauses.status, other);
  signed char status = *status_ptr;
  *status_ptr = -1;

  size_t *other_deletion = 0;

  // Allocate deletion tracking information if needed.

  if (track) {
    ADJUST (clauses.deleted, other);
    other_deletion = &ACCESS (clauses.deleted, other);
  }

  // First check the two problematic cases, where the clause
  // requested to be deleted was never added or if it was added but
  // is already deleted.

  if (!status) { // Never added.

    if (!last_clause_added_in_cnf && !first_clause_added_in_proof)
      ignored_deletions++; // No CNF and no clause added (yet).
    else if (relax)
      ignored_deletions++;
    else
      prr ("deleted clause '%d' at %s %zu "
           "is neither an original clause nor has been added "
           "(use '--relax' to ignore such deletions)",
           other, binary ? "byte" : "line", info);

  } else if (status < 0) { // Already deleted.

    if (relax)
      ignored_deletions++;
    else if (track) {
      assert (*other_deletion);
      prr ("clause %d requested to be deleted at %s %zu "
           "was already deleted at %s %zu "
           "(use '--relax' to ignore such deletions)",
           other, binary ? "byte" : "line", info, binary ? "byte" : "line",
           *other_deletion);
    } else
      prr ("clause %d requested to be deleted "
           "at %s %zu was already deleted before "
           "(use '--relax' to ignore such deletions and "
           "with '--track' for more information)",
           other, binary ? "byte" : "line", info);
  }

  // Deletion tracking information needs to be set if tracking is
  // requested and the clause was never added or got now deleted.

  if (track && status >= 0) {
    dbg ("marked clause %d to be deleted at %s %zu", other,
         binary ? "byte" : "line", info);
    *other_deletion = info;
  }

  if (status >= 0) {
    if (is_original_clause (other))
      statistics.original.cnf.deleted++;
    else
      statistics.original.proof.deleted++;
  }

  // We want to delete the literals of the deleted clause eagerly as
  // early as possible to save memory, i.e., while forward checking.

  bool delete_literals_eagerly;
  if (checking)
    delete_literals_eagerly = forward;
  else
    delete_literals_eagerly = !trimming;

  if (delete_literals_eagerly) {

    assert (!proof.output);
    assert (!cnf.output);

    assert (EMPTY (clauses.antecedents));

    // TODO the logic here needs documentation!!!!

    if (!relax || other < SIZE (clauses.literals)) {

      int **l = &ACCESS (clauses.literals, other);
      free (*l);
      *l = 0;
    }
  }

#if !defined(NDEBUG) || defined(LOGGING)
  PUSH (parsed_antecedents, other);
#endif
}

static void parse_proof () {
  double start = process_time ();
  vrb ("starting parsing proof after %.2f seconds", start);
  assert (proof.input);
  input = *proof.input;
  msg ("reading proof from '%s'", input.path);

  int ch = read_first_char ();
  while (ch == 'c' || ch == 's' || ch == 'v') {
    read_until_new_line ();
    ch = read_ascii ();
  }
  if (ch == 'a' || ch == 'd') {
    vrb ("first character '%c' indicates binary proof format", ch);
    input.binary = true;
  } else if (ISDIGIT (ch)) {
    vrb ("first character '%c' indicates ASCII proof format", ch);
    assert (!input.binary);
  } else if (ch == 'p')
    prr ("unexpected 'p': "
         "did you use a CNF instead of a proof file?");
  else if (ch != EOF) {
    if (isprint (ch))
      prr ("unexpected first character '%c'", ch);
    else
      prr ("unexpected first byte '0x%02x'", (unsigned) ch);
  }

  // To track in the binary proof format we use byte offsets instead of line
  // numbers.  This information is used in debugging and error messages and
  // 'trick' is used to tell this difference (using 'byte' vs. 'line').  For
  // the binary format we also do not have deletion line identifiers.

  const bool binary = input.binary;

  int last_id = 0;

  while (ch != EOF) {

    if (ch == 'c' || ch == 's' || ch == 'v') {
      read_until_new_line ();
      goto READ_NEXT_CH;
      continue;
    }

    const size_t info = (binary ? input.bytes : input.lines) + 1;
    int id, type = 0;

    if (binary) {
      if (ch != 'a' && ch != 'd')
        prr ("expected either 'a' or 'd'");
      type = ch;
      if (ch == 'a') {
        ch = read_binary ();
        if (ch == EOF)
          prr ("end-of-file after '%c'", type);
        if (!ch)
          prr ("invalid zero clause identifier '0' in addition");
        unsigned uid = 0, shift = 0;
        for (;;) {
          unsigned uch = ch;
          if (shift == 28 && (uch & ~15u))
            prr ("excessive clause identifier");
          uid |= (uch & 127) << shift;
          if (!(uch & 128))
            break;
          shift += 7;
          ch = read_binary ();
          if (!ch)
            prr ("invalid zero byte in clause identifier");
          if (ch == EOF)
            prr ("end-of-file parsing clause identifier");
        }
        if (uid & 1)
          prr ("negative identifier in clause addition");
        uid >>= 1;
        if (uid > (unsigned) INT_MAX)
          prr ("clause identifier %u too large", uid);
        id = uid;
        dbg ("parsed clause identifier %d at byte %zu", id, info);
      } else
        id = last_id;
    } else { // !binary
      if (!ISDIGIT (ch))
        prr ("expected digit as first character of line");
      id = ch - '0';
      while (ISDIGIT (ch = read_ascii ())) {
        if (!id)
          prr ("unexpected digit '%c' after '0'", ch);
        if (INT_MAX / 10 < id)
        LINE_IDENTIFIER_EXCEEDS_INT_MAX:
          prr ("line identifier '%s' exceeds 'INT_MAX'",
               exceeds_int_max (id, ch));
        id *= 10;
        int digit = ch - '0';
        if (INT_MAX - digit < id) {
          id /= 10;
          goto LINE_IDENTIFIER_EXCEEDS_INT_MAX;
        }
        id += digit;
      }
      if (ch != ' ')
        prr ("expected space after identifier '%d'", id);
      dbg ("parsed clause identifier %d at line %zu", id, info);
      ch = read_ascii ();
      if (ch == 'd') {
        ch = read_ascii ();
        if (ch != ' ')
          prr ("expected space after '%d d'", id);
        type = 'd';
      } else
        type = 'a';
    }
    if (id < last_id)
      prr ("identifier '%d' smaller than last '%d'", id, last_id);
    ADJUST (clauses.status, id);
    if (type == 'd') {
      assert (EMPTY (parsed_antecedents));
      int last = 0;
      if (binary) {
        do {
          int other;
          ch = read_binary ();
          if (ch == EOF)
            prr ("end-of-file before zero byte in deletion");
          if (ch & 1)
            prr ("invalid negative antecedent in deletion");
          if (ch) {
            unsigned uother = 0, shift = 0;
            for (;;) {
              unsigned uch = ch;
              if (shift == 28 && (uch & ~15u))
                prr ("excessive antecedent in deletion");
              uother |= (uch & 127) << shift;
              if (!(uch & 128))
                break;
              shift += 7;
              ch = read_binary ();
              if (!ch)
                prr ("invalid zero byte in antecedent deletion");
              if (ch == EOF)
                prr ("end-of-file parsing antecedent in deletion");
            }
            other = (uother >> 1);
          } else
            other = 0;
          if (other)
            delete_antecedent (other, binary, info);
          last = other;
        } while (last);
      } else { // !binary
        do {
          int other;
          ch = read_ascii ();
          if (!ISDIGIT (ch)) {
            if (last)
              prr ("expected digit after '%d ' in deletion", last);
            else
              prr ("expected digit after '%d d ' in deletion", id);
          }
          other = ch - '0';
          while (ISDIGIT ((ch = read_ascii ()))) {
            if (!other)
              prr ("unexpected digit '%c' after '0' in deletion", ch);
            if (INT_MAX / 10 < other)
            DELETED_CLAUSE_IDENTIFIER_EXCEEDS_INT_MAX:
              prr ("deleted clause identifier '%s' exceeds 'INT_MAX'",
                   exceeds_int_max (other, ch));
            other *= 10;
            int digit = ch - '0';
            if (INT_MAX - digit < other) {
              other /= 10;
              goto DELETED_CLAUSE_IDENTIFIER_EXCEEDS_INT_MAX;
            }
            other += digit;
          }
          if (other) {
            if (ch != ' ')
              prr ("expected space after '%d' in deletion", other);
            if (id && other > id)
              prr ("deleted clause '%d' "
                   "larger than deletion identifier '%d'",
                   other, id);
          } else if (ch != '\n')
            prr ("expected new-line after '0' at end of deletion");
          if (other)
            delete_antecedent (other, binary, info);
          last = other;
        } while (last);
      }
#if !defined(NDEBUG) || defined(LOGGING)
      PUSH (parsed_antecedents, 0);
      dbgs (parsed_antecedents.begin,
            "parsed deletion and deleted clauses");
      CLEAR (parsed_antecedents);
#endif
    } else {
      assert (type == 'a'); // Adding a clause code starts here.
      if (id == last_id)
        prr ("line identifier '%d' of addition line does not increase", id);
      if (!first_clause_added_in_proof) {
        if (last_clause_added_in_cnf) {
          if (last_clause_added_in_cnf == id)
            prr ("first added clause %d in proof "
                 "has same identifier as last original clause",
                 id);
          else if (last_clause_added_in_cnf > id)
            prr ("first added clause %d in proof "
                 "has smaller identifier as last original clause %d",
                 id, last_clause_added_in_cnf);
        }
        vrb ("adding first clause %d in proof", id);
        first_clause_added_in_proof = id;
        if (!last_clause_added_in_cnf) {
          signed char *begin = clauses.status.begin;
          signed char *end = begin + id;
          for (signed char *p = begin + 1; p != end; p++) {
            signed char status = *p;
            if (status)
              assert (status < 0);
            else
              *p = 1;
          }
          assert (!statistics.original.cnf.added);
          statistics.original.cnf.added = id - 1;
        }
      }
      assert (EMPTY (parsed_literals));
      if (binary) {
        for (;;) {
          ch = read_binary ();
          if (ch == EOF)
            prr ("end-of-file before terminating "
                 "zero byte in literals of clause %d",
                 id);
          if (!ch) {
            PUSH (parsed_literals, 0);
            break;
          }
          unsigned uidx = 0, shift = 0;
          for (;;) {
            unsigned uch = ch;
            if (shift == 28 && (uch & ~15u))
              prr ("excessive literal in clause %d", id);
            uidx |= (uch & 127) << shift;
            if (!(uch & 128))
              break;
            shift += 7;
            ch = read_binary ();
            if (!ch)
              prr ("invalid zero byte in literal of clause %d", id);
            if (ch == EOF)
              prr ("end-of-file parsing literal in clause %d", id);
          }
          int idx = (uidx >> 1);
          int lit = (uidx & 1) ? -idx : idx;
          PUSH (parsed_literals, lit);
        }
      } else { // !binary
        int last = id;
        assert (last);
        bool first = true;
        while (last) {
          int sign;
          if (first)
            first = false;
          else
            ch = read_ascii ();
          if (ch == '-') {
            if (!ISDIGIT (ch = read_ascii ()))
              prr ("expected digit after '%d -' in clause %d", last, id);
            if (ch == '0')
              prr ("expected non-zero digit after '%d -'", last);
            sign = -1;
          } else if (!ISDIGIT (ch))
            prr ("expected literal or '0' after '%d ' in clause %d", last,
                 id);
          else
            sign = 1;
          int idx = ch - '0';
          while (ISDIGIT (ch = read_ascii ())) {
            if (!idx)
              prr ("unexpected second '%c' after '%d 0' in clause %d", ch,
                   last, id);
            if (INT_MAX / 10 < idx) {
            VARIABLE_INDEX_EXCEEDS_INT_MAX:
              if (sign < 0)
                prr ("variable index in literal '-%s' "
                     "exceeds 'INT_MAX' in clause %d",
                     exceeds_int_max (idx, ch), id);
              else
                prr ("variable index '%s' exceeds 'INT_MAX' in clause %d",
                     exceeds_int_max (idx, ch), id);
            }
            idx *= 10;
            int digit = ch - '0';
            if (INT_MAX - digit < idx) {
              idx /= 10;
              goto VARIABLE_INDEX_EXCEEDS_INT_MAX;
            }
            idx += digit;
          }
          int lit = sign * idx;
          if (ch != ' ') {
            if (idx)
              prr ("expected space after literal '%d' in clause %d", lit,
                   id);
            else
              prr ("expected space after literals and '0' in clause %d",
                   id);
          }
          PUSH (parsed_literals, lit);
          last = lit;
        }
      }
      dbgs (parsed_literals.begin, "clause %d literals", id);

      size_t size_literals = SIZE (parsed_literals);
      size_t bytes_literals = size_literals * sizeof (int);
      int *l = malloc (bytes_literals);
      if (!l) {
        assert (size_literals);
        die ("out-of-memory allocating literals of size %zu clause %d",
             size_literals - 1, id);
      }
      memcpy (l, parsed_literals.begin, bytes_literals);
      ADJUST (clauses.literals, id);
      ACCESS (clauses.literals, id) = l;
      if (size_literals == 1) {
        if (!empty_clause) {
          vrb ("found empty clause %d", id);
          statistics.clauses.checked.empty++;
          empty_clause = id;
        }
      }

      CLEAR (parsed_literals);
      assert (EMPTY (parsed_antecedents));

      if (binary) {
        for (;;) {
          ch = read_binary ();
          if (ch == EOF)
            prr ("end-of-file instead of antecedent in clause %d", id);
          if (!ch) {
            PUSH (parsed_antecedents, 0);
            break;
          }
          unsigned uother = 0, shift = 0;
          for (;;) {
            unsigned uch = ch;
            if (shift == 28 && (uch & ~15u))
              prr ("excessive antecedent in clause %d", id);
            uother |= (uch & 127) << shift;
            if (!(uch & 128))
              break;
            shift += 7;
            ch = read_binary ();
            if (!ch)
              prr ("invalid zero byte in clause %d", id);
            if (ch == EOF)
              prr ("end-of-file parsing antecedent in clause %d", id);
          }
          int other = (uother >> 1);
          int signed_other = (uother & 1) ? -other : other;
          if (other) {
            if (other >= id)
              prr ("antecedent '%d' in clause %d exceeds clause",
                   signed_other, id);
            signed char status = ACCESS (clauses.status, other);
            if (!status)
              prr ("antecedent '%d' in clause %d "
                   "is neither an original clause nor has been added",
                   signed_other, id);
            else if (status < 0) {
              if (track) {
                size_t info = ACCESS (clauses.deleted, other);
                assert (info);
                prr ("antecedent %d in clause %d was deleted at %s %zu",
                     signed_other, id, binary ? "byte" : "clause", info);
              } else
                prr ("antecedent %d in clause %d was deleted before "
                     "(run with '--track' for more information)",
                     other, id);
            }
          }
          PUSH (parsed_antecedents, signed_other);
        }
      } else { // !binary
        int last = 0;
        assert (!last);
        do {
          int sign;
          if ((ch = read_ascii ()) == '-') {
            if (!ISDIGIT (ch = read_ascii ()))
              prr ("expected digit after '%d -' in clause %d", last, id);
            if (ch == '0')
              prr ("expected non-zero digit after '%d -'", last);
            sign = -1;
          } else if (!ISDIGIT (ch))
            prr ("expected clause identifier after '%d ' "
                 "in clause %d",
                 last, id);
          else
            sign = 1;
          int other = ch - '0';
          while (ISDIGIT (ch = read_ascii ())) {
            if (!other)
              prr ("unexpected second '%c' after '%d 0' in clause %d", ch,
                   last, id);
            if (INT_MAX / 10 < other) {
            ANTECEDENT_IDENTIFIER_EXCEEDS_INT_MAX:
              if (sign < 0)
                prr ("antecedent '-%s' exceeds 'INT_MAX' in clause %d",
                     exceeds_int_max (other, ch), id);
              else
                prr ("antecedent '%s' exceeds 'INT_MAX' in clause %d",
                     exceeds_int_max (other, ch), id);
            }
            other *= 10;
            int digit = ch - '0';
            if (INT_MAX - digit < other) {
              other /= 10;
              goto ANTECEDENT_IDENTIFIER_EXCEEDS_INT_MAX;
            }
            other += digit;
          }
          int signed_other = sign * other;
          if (other) {
            if (ch != ' ')
              prr ("expected space after antecedent '%d' in clause %d",
                   signed_other, id);
            if (other >= id)
              prr ("antecedent '%d' in clause %d exceeds clause",
                   signed_other, id);
            signed char status = ACCESS (clauses.status, other);
            if (!status)
              prr ("antecedent '%d' in clause %d "
                   "is neither an original clause nor has been added",
                   signed_other, id);
            else if (status < 0) {
              if (track) {
                size_t info = ACCESS (clauses.deleted, other);
                assert (info);
                prr ("antecedent %d in clause %d was deleted at %s %zu",
                     signed_other, id, binary ? "byte" : "clause", info);
              } else
                prr ("antecedent %d in clause %d was deleted before "
                     "(run with '--track' for more information)",
                     other, id);
            }
          } else {
            if (ch != '\n')
              prr ("expected new-line after '0' at end of clause %d", id);
          }
          PUSH (parsed_antecedents, signed_other);
          last = signed_other;
        } while (last);
      }
      dbgs (parsed_antecedents.begin, "clause %d antecedents", id);
      size_t size_antecedents = SIZE (parsed_antecedents);
      assert (size_antecedents > 0);
      if (track) {
        ADJUST (clauses.added, id);
        size_t *addition = &ACCESS (clauses.added, id);
        *addition = info;
      }
      statistics.original.proof.added++;
      if (checking && forward) {
        check_clause (id, l, parsed_antecedents.begin);
        dbg ("forward checked clause %d", id);
      } else if (trimming || checking) {
        size_t bytes_antecedents = size_antecedents * sizeof (int);
        int *a = malloc (bytes_antecedents);
        if (!a) {
          assert (size_antecedents);
          die ("out-of-memory allocating antecedents of size %zu clause "
               "%d",
               size_antecedents - 1, id);
        }
        memcpy (a, parsed_antecedents.begin, bytes_antecedents);
        ADJUST (clauses.antecedents, id);
        ACCESS (clauses.antecedents, id) = a;
      }
      CLEAR (parsed_antecedents);
      ACCESS (clauses.status, id) = 1;
    }
    last_id = id;
  READ_NEXT_CH:
    if (binary) {
      ch = read_binary ();
      input.lines++;
    } else
      ch = read_ascii ();
  }
  RELEASE (parsed_antecedents);
  RELEASE (parsed_literals);
  if (input.close)
    fclose (input.file);
  *proof.input = input;

  RELEASE (clauses.deleted);
  RELEASE (clauses.added);
  RELEASE (clauses.status);

  if (!empty_clause) {
    if (cnf.input)
      wrn ("no empty clause added in input CNF nor input proof");
    else
      wrn ("no empty clause added in input proof");
  }

  vrb ("read %zu proof lines with %s", input.lines,
       pretty_bytes (input.bytes));

  msg ("parsed original proof with %zu added and %zu deleted clauses",
       statistics.original.proof.added, statistics.original.proof.deleted);

  if (ignored_deletions)
    vrb ("ignored %zu deleted clauses", ignored_deletions);
  else
    vrb ("no clause deletions had to be ignored");

  double end = process_time (), duration = end - start;
  vrb ("finished parsing proof after %.2f seconds", end);
  msg ("parsing original proof took %.2f seconds and needed %.0f MB "
       "memory",
       duration, mega_bytes ());
}

static inline bool mark_used (int id, int used_where) {
  assert (0 < id);
  assert (0 < used_where);
  int *w = &ACCESS (clauses.used, id);
  int used_before = *w;
  if (used_before >= used_where)
    return true;
  *w = used_where;
  dbg ("updated clause %d to be used in clause %d", id, used_where);
  if (used_before)
    return true;
  if (is_original_clause (id))
    statistics.trimmed.cnf.added++;
  else
    statistics.trimmed.proof.added++;
  return false;
}

static void trim_proof () {

  if (!trimming)
    return;

  double start = process_time ();
  vrb ("starting trimming after %.2f seconds", start);

  ADJUST (clauses.used, empty_clause);

  static struct int_stack work;
  ZERO (work);

  if (empty_clause) {
    assert (EMPTY (work));
    mark_used (empty_clause, empty_clause);
    if (!is_original_clause (empty_clause))
      PUSH (work, empty_clause);

    while (!EMPTY (work)) {
      unsigned id = POP (work);
      assert (ACCESS (clauses.used, id));
      int *a = ACCESS (clauses.antecedents, id);
      assert (a);
      for (int *p = a, other; (other = abs (*p)); p++)
        if (!mark_used (other, id) && !is_original_clause (other))
          PUSH (work, other);
    }
  }

  msg ("trimmed %zu original clauses in CNF to %zu clauses %.0f%%",
       statistics.original.cnf.added, statistics.trimmed.cnf.added,
       percent (statistics.trimmed.cnf.added,
                statistics.original.cnf.added));

  msg ("trimmed %zu added clauses in original proof to %zu clauses %.0f%%",
       statistics.original.proof.added, statistics.trimmed.proof.added,
       percent (statistics.trimmed.proof.added,
                statistics.original.proof.added));

  RELEASE (work);

  double end = process_time (), duration = end - start;
  vrb ("finished trimming after %.2f seconds", end);
  msg ("trimming proof took %.2f seconds", duration);
}

static void check_proof () {

  if (!checking || forward || !empty_clause)
    return;

  if (empty_clause && (!first_clause_added_in_proof ||
                       empty_clause < first_clause_added_in_proof))
    return;

  double start = process_time ();
  vrb ("starting backward checking after %.2f seconds", start);

  int id = first_clause_added_in_proof;
  for (;;) {
    int where = trimming ? ACCESS (clauses.used, id) : -1;
    if (where) {
      int *l = ACCESS (clauses.literals, id);
      int *a = ACCESS (clauses.antecedents, id);
      dbgs (l, "checking clause %d literals", id);
      dbgs (a, "checking clause %d antecedents", id);
      check_clause (id, l, a);
    }
    if (id++ == empty_clause)
      break;
  }

  double end = process_time (), duration = end - start;
  vrb ("finished backward checking after %.2f seconds", end);
  msg ("backward checking proof took %.2f seconds", duration);
}

static struct file *write_file (struct file *file) {
  assert (file->path);
  if (!strcmp (file->path, "/dev/null")) {
    assert (!file->file);
    assert (!file->close);
  } else if (!strcmp (file->path, "-")) {
    file->file = stdout;
    file->path = "<stdout>";
    assert (!file->close);
  } else if (!(file->file = fopen (file->path, "w")))
    die ("can not write '%s'", file->path);
  else
    file->close = 1;
  return file;
}

static int map_id (int id) {
  assert (id != INT_MIN);
  int abs_id = abs (id);
  int res;
  if (abs_id < first_clause_added_in_proof)
    res = id;
  else {
    res = ACCESS (clauses.map, abs_id);
    if (id < 0)
      res = -res;
  }
  return res;
}

static void write_non_empty_proof () {

  assert (output.path);

  assert (empty_clause > 0);
  ADJUST (clauses.links, empty_clause);
  ADJUST (clauses.heads, empty_clause);

  for (int id = 1; id != first_clause_added_in_proof; id++) {
    int where = ACCESS (clauses.used, id);
    if (where) {
      assert (id < where);
      assert (!is_original_clause (where));
      ACCESS (clauses.links, id) = ACCESS (clauses.heads, where);
      ACCESS (clauses.heads, where) = id;
    } else {
      if (!statistics.trimmed.cnf.deleted) {
        if (ascii) {
          write_int (first_clause_added_in_proof - 1);
          write_str (" d");
        } else
          write_binary ('d');
      }
      if (ascii) {
        write_space ();
        write_int (id);
      } else
        write_signed (id);
      statistics.trimmed.cnf.deleted++;
    }
  }

  if (statistics.trimmed.cnf.deleted) {
    if (ascii)
      write_str (" 0\n");
    else {
      write_binary (0);
      output.lines++;
    }

    vrb ("deleting %zu original CNF clauses initially",
         statistics.trimmed.cnf.deleted);
  }

  ADJUST (clauses.map, empty_clause);

  int id = first_clause_added_in_proof;
  int mapped = id;

  for (;;) {
    int where = ACCESS (clauses.used, id);
    if (where) {
      if (id != empty_clause) {
        assert (id < where);
        ACCESS (clauses.links, id) = ACCESS (clauses.heads, where);
        ACCESS (clauses.heads, where) = id;
        ACCESS (clauses.map, id) = mapped;
      }
      if (ascii)
        write_int (mapped);
      else {
        write_binary ('a');
        write_signed (mapped);
      }
      int *l = ACCESS (clauses.literals, id);
      assert (l);
      if (ascii) {
        for (const int *p = l; *p; p++)
          write_space (), write_int (*p);
        write_str (" 0");
      } else {
        for (const int *p = l; *p; p++)
          write_signed (*p);
        write_binary (0);
      }
      int *a = ACCESS (clauses.antecedents, id);
      assert (a);
      if (ascii) {
        for (const int *p = a; *p; p++) {
          write_space ();
          int other = *p;
          assert (abs (other) < id);
          int mapped = map_id (other);
          assert ((other < 0) == (mapped < 0));
          write_int (mapped);
        }
        write_str (" 0\n");
      } else {
        for (const int *p = a; *p; p++) {
          int other = *p;
          assert (abs (other) < id);
          int mapped = map_id (other);
          assert ((other < 0) == (mapped < 0));
          write_signed (mapped);
        }
        write_binary (0);
      }
      int head = ACCESS (clauses.heads, id);
      if (head) {
        if (ascii) {
          write_int (mapped);
          write_str (" d");
          for (int link = head, next; link; link = next) {
            if (is_original_clause (link))
              statistics.trimmed.cnf.deleted++;
            else
              statistics.trimmed.proof.deleted++;
            write_space ();
            write_int (map_id (link));
            next = ACCESS (clauses.links, link);
          }
          write_str (" 0\n");
        } else {
          write_binary ('d');
          for (int link = head, next; link; link = next) {
            if (is_original_clause (link))
              statistics.trimmed.cnf.deleted++;
            else
              statistics.trimmed.proof.deleted++;
            write_signed (map_id (link));
            next = ACCESS (clauses.links, link);
          }
          write_binary (0);
        }
      }
      mapped++;
    }
    if (id++ == empty_clause)
      break;
  }
}

static void write_empty_proof () {
  msg ("writing empty proof without empty clause in input proof");
}

static void write_proof () {
  if (!proof.output)
    return;

  double start = process_time ();
  vrb ("starting writing proof after %.2f seconds", start);

  buffer.pos = 0;
  output = *write_file (proof.output);
  msg ("writing proof to '%s'", output.path);
  if (empty_clause)
    write_non_empty_proof ();
  else
    write_empty_proof ();

  assert (proof.output);
  flush_buffer ();
  if (output.close)
    fclose (output.file);
  *proof.output = output;

  msg ("trimmed %s to %s %.0f%%", pretty_bytes (proof.input->bytes),
       pretty_bytes (proof.output->bytes),
       percent (proof.output->bytes, proof.input->bytes));

  double end = process_time (), duration = end - start;
  vrb ("finished writing proof after %.2f seconds", end);
  msg ("writing proof took %.2f seconds", duration);
}

static void write_clause (int id) {
  int *l = ACCESS (clauses.literals, id);
  for (int *p = l, lit; (lit = *p); p++)
    write_int (*p), write_space ();
  write_str ("0\n");
}

static void write_cnf () {
  if (!cnf.output)
    return;
  double start = process_time ();
  vrb ("starting writing CNF after %.2f seconds", start);
  buffer.pos = 0;
  output = *write_file (cnf.output);
  msg ("writing CNF to '%s'", output.path);

  write_str ("p cnf ");
  write_int (variables.original);
  write_space ();
  assert (trimming);
  size_t count = 0;
  write_size_t (statistics.trimmed.cnf.added);
  write_ascii ('\n');
  int id = 0;
  while (id++ != last_clause_added_in_cnf)
    if (id <= empty_clause && ACCESS (clauses.used, id))
      write_clause (id), count++;
  assert (count == statistics.trimmed.cnf.added);
  msg ("wrote %zu clauses to CNF", count);

  flush_buffer ();
  if (output.close)
    fclose (output.file);
  *cnf.output = output;

  vrb ("wrote %zu proof lines of %s", output.lines,
       pretty_bytes (output.bytes));
  msg ("trimmed %s to %s %.0f%%", pretty_bytes (cnf.input->bytes),
       pretty_bytes (cnf.output->bytes),
       percent (cnf.output->bytes, cnf.input->bytes));

  double end = process_time (), duration = end - start;
  vrb ("finished writing CNF after %.2f seconds", end);
  msg ("writing to CNF took %.2f seconds", duration);
}

static void release () {
#ifndef NDEBUG
  RELEASE (clauses.heads);
  RELEASE (clauses.links);
  RELEASE (clauses.map);
  RELEASE (clauses.used);
  if (strict)
    RELEASE (variables.marks);
  else
    RELEASE (variables.values);
  RELEASE (trail);
  release_ints_map (&clauses.literals);
  release_ints_map (&clauses.antecedents);
#endif
}

static const char *numeral (size_t i) {
  if (i == 0)
    return "1st";
  if (i == 1)
    return "2nd";
  if (i == 2)
    return "3rd";
  assert (i == 3);
  return "4th";
}

static void options (int argc, char **argv) {
  for (int i = 1; i != argc; i++) {
    const char *arg = argv[i];
    if (!strcmp (arg, "-h") || !strcmp (arg, "--help")) {
      fputs (usage, stdout);
      exit (0);
    }
    if (!strcmp (arg, "-a") || !strcmp (arg, "--ascii") ||
        !strcmp (arg, "--no-binary"))
      ascii = arg;
    else if (!strcmp (arg, "-f") || !strcmp (arg, "--force"))
      force = arg;
    else if (!strcmp (arg, "-S") || !strcmp (arg, "--forward"))
      forward = arg;
    else if (!strcmp (arg, "-l") || !strcmp (arg, "--log"))
#ifdef LOGGING
      verbosity = INT_MAX;
#else
      die ("invalid option '-l' (build without logging support)");
#endif
    else if (!strcmp (arg, "-q") || !strcmp (arg, "--quiet"))
      verbosity = -1;
    else if (!strcmp (arg, "-s") || !strcmp (arg, "--strict"))
      strict = arg;
    else if (!strcmp (arg, "-t") || !strcmp (arg, "--track"))
      track = arg;
    else if (!strcmp (arg, "-v") || !strcmp (arg, "--verbose")) {
      if (verbosity <= 0)
        verbosity = 1;
    } else if (!strcmp (arg, "--no-check"))
      nocheck = arg;
    else if (!strcmp (arg, "--no-trim"))
      notrim = arg;
    else if (!strcmp (arg, "--relax"))
      relax = true;
    else if (!strcmp (arg, "-V") || !strcmp (arg, "--version"))
      fputs (version, stdout), fputc ('\n', stdout), exit (0);
    else if (arg[0] == '-' && arg[1])
      die ("invalid option '%s' (try '-h')", arg);
    else if (size_files == 4)
      die ("too many files '%s', '%s', '%s' and '%s' (try '-h')",
           files[0].path, files[1].path, files[2].path, arg);
    else
      files[size_files++].path = arg;
  }

  if (!size_files)
    die ("no input file given (try '-h')");

  if (size_files > 2 && notrim)
    die ("can not write to '%s' with '%s'", files[2].path, notrim);

  for (size_t i = 0; i + 1 != size_files; i++)
    if (strcmp (files[i].path, "-") && strcmp (files[i].path, "/dev/null"))
      for (size_t j = i + 1; j != size_files; j++)
        if (!strcmp (files[i].path, files[j].path))
          die ("identical %s and %s file '%s'", numeral (i), numeral (j),
               files[i].path);

  if (size_files > 2 && !strcmp (files[0].path, "-") &&
      !strcmp (files[1].path, "-"))
    die ("can not use '<stdin>' for both first two input files");

  if (size_files == 4 && !strcmp (files[2].path, "-") &&
      !strcmp (files[3].path, "-"))
    die ("can not use '<stdout>' for both last two output files");
}

static struct file *read_file (struct file *file) {
  assert (file->path);
  if (!strcmp (file->path, "/dev/null")) {
    assert (!file->file);
    assert (!file->close);
  } else if (!strcmp (file->path, "-")) {
    file->file = stdin;
    file->path = "<stdin>";
    assert (!file->close);
  } else if (!(file->file = fopen (file->path, "r")))
    die ("can not read '%s'", file->path);
  else
    file->close = 1;
  file->saved = EOF;
  return file;
}

static bool has_suffix (const char *str, const char *suffix) {
  size_t l = strlen (str), k = strlen (suffix);
  return l >= k && !strcasecmp (str + l - k, suffix);
}

static bool looks_like_a_dimacs_file (const char *path) {
  assert (path);
  if (!strcmp (path, "-"))
    return false;
  if (!strcmp (path, "/dev/null"))
    return false;
  if (has_suffix (path, ".cnf"))
    return true;
  if (has_suffix (path, ".dimacs"))
    return true;
#if 0
  if (has_suffix (path, ".cnf.gz"))
    return true;
  if (has_suffix (path, ".cnf.bz2"))
    return true;
  if (has_suffix (path, ".cnf.xz"))
    return true;
  if (has_suffix (path, ".dimacs.gz"))
    return true;
  if (has_suffix (path, ".dimacs.bz2"))
    return true;
  if (has_suffix (path, ".dimacs.xz"))
    return true;
#endif
  FILE *file = fopen (path, "r");
  if (!file)
    return false;
  int ch = getc (file);
  fclose (file);
  return ch == 'c' || ch == 'p';
}

static void open_input_files () {
  assert (size_files);
  if (size_files == 1)
    proof.input = read_file (&files[0]);
  else if (size_files == 2) {
    struct file *file = &files[0];
    input = *read_file (file);
    int ch;
    if (input.file) {
      while ((ch = getc (input.file)) == 'c') {
        input.bytes++;
        while ((ch = getc (input.file)) != '\n') {
          if (ch == EOF)
            prr ("unexpected end-of-file in comment before new-line");
          input.bytes++;
          if (ch == '\r') {
            ch = getc (input.file);
            if (ch != EOF)
              input.bytes++;
            if (ch == '\n')
              break;
            prr ("carriage-return without following new-line");
          }
        }
        input.lines++;
      }
      input.saved = ch;
    } else {
      assert (input.saved == EOF);
      ch = EOF;
    }
    *file = input;
    if (ch == 'p') {
      cnf.input = file;
      proof.input = read_file (&files[1]);
      if (force)
        wrn ("using '%s' with CNF as first file '%s' does not make sense",
             force, files[0].path);
    } else {
      proof.input = file;
      if (notrim)
        die ("can not write to '%s' with '%s'", files[1].path, notrim);
      if (looks_like_a_dimacs_file (files[1].path)) {
        if (force)
          wrn ("forced to overwrite second file '%s' with trimmed proof "
               "even though it looks like a CNF in DIMACS format",
               files[1].path);
        else
          die ("will not overwrite second file '%s' with trimmed proof "
               "as it looks like a CNF in DIMACS format (use '--force' to "
               "overwrite nevertheless)",
               files[1].path);
      }
      proof.output = &files[1];
    }
  } else {
    assert (2 < size_files);
    assert (size_files < 5);
    cnf.input = read_file (&files[0]);
    proof.input = read_file (&files[1]);
    proof.output = &files[2];
    if (size_files == 4)
      cnf.output = &files[3];
  }
  if (force && size_files != 2)
    wrn ("using '%s' without two files does not make sense", force);
  if (!cnf.input && nocheck)
    wrn ("using '%s' without CNF does not make sense", nocheck);
  if (!cnf.input && forward)
    wrn ("using '%s' without CNF does not make sense", forward);
  if (strict && nocheck)
    wrn ("using '%s' and '%s' does not make sense", strict, nocheck);
  if (strict && !cnf.input)
    wrn ("using '%s' without CNF does not make sense", strict);
  if (proof.output && forward)
    die ("can not write proof to '%s' with '%s'", proof.output->path,
         forward);
  if (!proof.output && ascii)
    wrn ("'%s' without output-proof does not make sense", ascii);
  if (proof.output && looks_like_a_dimacs_file (proof.output->path)) {
    if (force)
      wrn ("forced to write third file '%s' with trimmed proof "
           "even though it looks like a CNF in DIMACS format",
           files[2].path);
    else
      die ("will not write third file '%s' with trimmed proof "
           "as it looks like a CNF in DIMACS format (use '--force' to "
           "overwrite nevertheless)",
           files[2].path);
  }

  // No CNF output without proof output: this is a restriction due to the
  // way we specify files but would also make the internal logic of
  // running the various functions in different mode pretty complex.
  //
  assert (!cnf.output || proof.output);

  // Then we also enforce (above) that you can not do forward checking and
  // at the same time produce a proof.  With forward checking we want to
  // check on-the-fly and also at the same delete antecedent lists and
  // clauses on the fly too. This restriction (*) simplifies the logic.
  //
  assert (!proof.output || !forward);

  checking = !nocheck && cnf.input; // No checking without CNF for sure.
  trimming = !notrim && !forward;   // With the above restriction (*).
}

static void print_banner () {
  if (verbosity < 0)
    return;
  printf ("c LRAT-TRIM Version %s trims LRAT proofs\n"
          "c Copyright (c) 2023 Armin Biere University of Freiburg\n",
          version);
  fflush (stdout);
}

static void print_mode () {
  if (verbosity < 0)
    return;

  const char *mode;
  if (cnf.input) {
    if (proof.output) {
      if (cnf.output)
        mode = "reading CNF and LRAT files and writing them too";
      else
        mode = "reading CNF and LRAT files and writing LRAT file";
    } else {
      assert (!cnf.output);
      mode = "reading CNF and LRAT files";
    }
  } else {
    if (proof.output)
      mode = "reading and writing LRAT files";
    else
      mode = "only reading LRAT file";
  }
  printf ("c %s\n", mode);

  if (checking) {
    if (forward) {
      assert (!trimming);
      mode = "forward checking all clauses without trimming proof";
    } else if (trimming)
      mode = "backward checking trimmed clauses after trimming proof";
    else
      mode = "backward checking all clauses without trimming proof";
  } else {
    if (trimming)
      mode = "trimming proof without checking clauses";
    else
      mode = "neither trimming proof not checking clauses";
  }
  printf ("c %s\n", mode);

  fflush (stdout);
}

static void print_statistics () {
  double t = process_time ();
  if (checking) {
    msg ("checked %zu clauses %.0f per second",
         statistics.clauses.checked.total,
         average (statistics.clauses.checked.total, t));
    msg ("resolved %zu clauses %.2f per checked clause",
         statistics.clauses.resolved,
         average (statistics.clauses.resolved,
                  statistics.clauses.checked.total));
    if (strict)
      msg ("marked %zu literals %.2f per checked clause",
           statistics.literals.marked,
           average (statistics.literals.marked,
                    statistics.clauses.checked.total));
    else
      msg ("assigned %zu literals %.2f per checked clause",
           statistics.literals.assigned,
           average (statistics.literals.assigned,
                    statistics.clauses.checked.total));
  }
  msg ("maximum memory usage of %.0f MB", mega_bytes ());
  msg ("total time of %.2f seconds", t);
}

static void close_coverage () {
#ifdef COVERAGE
  printf ("c COVERED pretty_bytes (1<<30) = \"%s\"\n",
          pretty_bytes (1 << 30));
#endif
}

int main (int argc, char **argv) {
  options (argc, argv);
  open_input_files ();
  print_banner ();
  print_mode ();
  close_coverage ();
  parse_cnf ();
  parse_proof ();
  trim_proof ();
  check_proof ();
  write_proof ();
  write_cnf ();
  int res = 0;
  if (checking) {
    if (statistics.clauses.checked.empty) {
      printf ("s VERIFIED\n");
      fflush (stdout);
      res = 20;
    } else
      msg ("no empty clause found and checked");
  }
  release ();
  print_statistics ();
  return res;
}
