#include <algorithm>
#include <vector>

#include <cassert>
#include <climits>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>

#include <sys/resource.h>
#include <sys/time.h>

using namespace std;

struct Clause {
  int size, glue;
  long resolved;
  bool redundant, garbage;
  int literals[1];
};

struct Var {
  long bumped;
  bool seen, minimized, poison;
  int level;
  Var * prev, * next;
  Clause * reason;
  Var () :
    bumped (0),
    seen (false), minimized (false), poison (false),
    prev (0), next (0)
  { }
};

struct Watch {
  int blit;
  Clause * clause;
  Watch (int b, Clause * c) : blit (b), clause (c) { }
};

typedef vector<Watch> Watches;

static int max_var, num_original_clauses;

static Var * vars;
static signed char * vals, * phases;
static Watches * all_literal_watches;
static struct { Var * first, * last, * next; } queue;

static bool unsat;
static int level;
static vector<int> literals, trail;
static vector<Clause*> irredundant, redundant;
static Clause * conflict;

static long conflicts, decisions, restarts, propagations, bumped;

static struct { 
  struct { double glue, size; } resolved;
  struct { struct { double fast, slow; } glue; } learned;
} ema;

static FILE * input, * proof;
static int close_input, close_proof;
static const char * input_name, * proof_name;

static void msg (const char * fmt, ...) {
  va_list ap;
  fputs ("c ", stdout);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

#ifdef LOGGING

static void LOG (const char * fmt, ...) {
  va_list ap;
  printf ("c LOG %d ", level);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void LOG (Clause * c, const char *fmt, ...) {
  va_list ap;
  printf ("c LOG %d ", level);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  if (c) {
    if (c->redundant) printf (" redundant glue %d", c->glue);
    else printf (" irredundant");
    printf (" size %d clause", c->size);
    for (int i = 0; i < c->size; i++)
      printf (" %d", c->literals[i]);
  } else if (level) printf (" unit");
  else printf (" decision");
  fputc ('\n', stdout);
  fflush (stdout);
} while (0)

#else
#define LOG(ARGS...) do { } while (0)
#endif

static void die (const char * fmt, ...) {
  va_list ap;
  fputs ("*** cadical error: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static double seconds (void) {
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

static int val (int lit) {
  assert (lit), assert (abs (lit) <= max_var);
  int res = vals[abs (lit)];
  if (lit < 0) res = -res;
  return res;
}

static int sign (int lit) {
  assert (lit), assert (abs (lit) <= max_var);
  return lit < 0 ? -1 : 1;
}

static Watches & watches (int lit) {
  assert (lit), assert (abs (lit) <= max_var);
  return all_literal_watches[2*abs (lit) + (lit < 0)];
}

static Var & var (int lit) { return vars [abs (lit)]; }

static void assign (int lit, Clause * reason = 0) {
  assert (!val (lit));
  Var & v = var (lit);
  v.level = level;
  v.reason = reason;
  vals[abs (lit)] = sign (lit);
  assert (val (lit) > 0);
  trail.push_back (lit);
  LOG (reason, "assign %d", lit);
}

static void watch_literal (Clause * c, int lit, int blit) {
  watches (lit).push_back (Watch (blit, c));
  LOG (c, "watch %d blit %d in", lit, blit);
}

static void watch_clause (Clause * c) {
  assert (c->size > 1);
  int l0 = c->literals[0], l1 = c->literals[1];
  watch_literal (c, l0, l1);
  watch_literal (c, l1, l0);
}

static Clause * new_clause (bool red, int glue = 0) {
  assert (literals.size () <= (size_t) INT_MAX);
  int size = (int) literals.size ();
  Clause * res = (Clause*) new char[sizeof *res + sizeof (int)];
  res->size = size;
  res->glue = glue;
  res->resolved = conflicts;
  res->redundant = red;
  res->garbage = false;
  for (int i = 0; i < size; i++) res->literals[i] = literals[i];
  res->literals[size] = 0;
  if (red) redundant.push_back (res);
  else irredundant.push_back (res);
  LOG (res, "new");
  return res;
}

static void add_new_original_clause () {
  int size = (int) literals.size ();
  if (!size) {
    if (!unsat) msg ("original empty clause"), unsat = true;
    else LOG ("original empty clause produces another inconsistency");
  } else if (size == 1) {
    int unit = literals[0], tmp = val (unit);
    if (!tmp) assign (unit);
    else if (tmp < 0) {
      if (!unsat) msg ("parsed clashing unit"), unsat = true;
      else LOG ("original clashing unit produces another inconsistency");
    } else LOG ("original redundant unit");
  } else watch_clause (new_clause (false));
}

static Clause * new_learned_clause (int g) { return new_clause (true, g); }

static void delete_clause (Clause * c) { 
  LOG (c, "delete");
  delete [] (char*) c;
}

static int solve () {
  return 0;
}

static void init_queue () {
  Var * prev = 0;
  for (int i = 1; i <= max_var; i++) {
    Var * v = &vars[i];
    if ((v->prev = prev)) prev->next = v;
    else queue.first = v;
    prev = v;
  }
  queue.last = queue.next = prev;
}

static void init () {
  vals = new signed char[max_var + 1];
  phases = new signed char[max_var + 1];
  vars = new Var[max_var + 1];
  all_literal_watches = new Watches[2*(max_var + 1)];
  for (int i = 1; i <= max_var; i++) vals[i] = 0;
  for (int i = 1; i <= max_var; i++) phases[i] = -1;
  init_queue ();
  msg ("initialized %d variables", max_var);
}

static void reset () {
  for (size_t i = 0; i < irredundant.size (); i++)
    delete_clause (irredundant[i]);
  for (size_t i = 0; i < redundant.size (); i++)
    delete_clause (redundant[i]);
  delete [] all_literal_watches;
  delete [] vars;
  delete [] vals;
}

/*------------------------------------------------------------------------*/

static bool has_suffix (const char * str, const char * suffix) {
  int k = strlen (str), l = strlen (suffix);
  return k > l && !strcmp (str + k - l, suffix);
}

static FILE * read_pipe (const char * fmt, const char * path) {
  char * cmd = (char*) malloc (strlen (fmt) + strlen (path));
  sprintf (cmd, fmt, path);
  FILE * res = popen (cmd, "r");
  free (cmd);
  return res;
}

static const char * USAGE =
"usage: cadical [ -h ] [ <input> [ <proof> ] ]\n"
"\n"
"where '<input>' is a (compressed) DIMACS file and '<output>'\n"
"is a file to store the DRAT proof.  If no '<proof>' file is\n"
"specified, then no proof is generated.  If no '<input>' is given\n"
"then '<stdin>' is used. If '-' is used as '<input>' then the\n"
"solver reads from '<stdin>'.  If '-' is specified for '<proof>'\n"
"then the proof is generated and printed to '<stdout>'.\n";

struct lit_less_than {
  bool operator () (const int a, const int b) const {
    int res = abs (a) - abs (b);
    if (res) return res;
    return a < b ? -1 : 1;
  }
};

static bool tautological () {
  sort (literals.begin (), literals.end (), lit_less_than ());
  size_t j = 0;
  int prev = 0;
  for (size_t i = 0; i < literals.size (); i++) {
    int lit = literals[i];
    if (lit == -prev) {
      return true;
    }
    if (lit != prev) literals[j++] = lit;
  }
  literals.resize (j);
  return true;
}

static void parse_dimacs () {
  int ch;
  for (;;) {
    ch = getc (input);
    if (ch != 'c') break;
    while ((ch = getc (input)) != '\n')
      if (ch == EOF)
	die ("unexpected end-of-file in header comment");
  }
  if (ch != 'p') die ("expected 'c' or 'p'");
  if (fscanf (input, " cnf %d %d", &max_var, &num_original_clauses) != 2 ||
      max_var < 0 || num_original_clauses < 0)
    die ("invalid 'p ...' header");
  msg ("found 'p cnf %d %d' header", max_var, num_original_clauses);
  init ();
  int lit = 0, parsed_clauses = 0;
  while (fscanf (input, "%d", &lit) == 1) {
    if (lit == INT_MIN || abs (lit) > max_var)
      die ("invalid literal %d", lit);
    if (lit) {
      if (literals.size () == INT_MAX) die ("clause too large");
      literals.push_back (lit);
    } else if (!tautological ()) add_new_original_clause ();
    else LOG ("tautological original clause");
    literals.clear ();
    if (parsed_clauses++ >= num_original_clauses) die ("too many clauses");
  }
  if (lit) die ("last clause without '0'");
  if (parsed_clauses < num_original_clauses) die ("clause missing");
  msg ("parsed %d clauses in %.2f seconds", parsed_clauses, seconds ());
}

static double relative (double a, double b) { return b ? a / b : 0; }

static void print_statistics () {
  double t = seconds ();
  msg ("");
  msg ("conflicts:    %22ld   %10.2f per second",
    conflicts, relative (conflicts, t));
  msg ("decisions:    %22ld   %10.2f per second",
    decisions, relative (decisions, t));
  msg ("restarts:     %22ld   %10.2f per second",
    restarts, relative (restarts, t));
  msg ("propagations: %22ld   %10.2f per second",
    propagations, relative (propagations, t));
  msg ("time:         %22s   %10.2f seconds", "", t);
  msg ("");
}

int main (int argc, char ** argv) {
  int i, res;
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h")) fputs (USAGE, stdout), exit (0);
    else if (!strcmp (argv[i], "-")) {
      if (proof) die ("too many arguments");
      else if (!input) input = stdin, input_name = "<stdin>";
      else proof = stdout, proof_name = "<stdout>";
    } else if (argv[i][0] == '-')
    die ("invalid option '%s'", argv[i]);
    else if (proof) die ("too many arguments");
    else if (input) {
      if (!(proof = fopen (argv[i], "w")))
	die ("can not open and write DRAT proof to '%s'", argv[i]);
      proof_name = argv[i], close_proof = 1;
    } else {
      if (has_suffix (argv[i], ".bz2"))
	input = read_pipe ("bzcat %s", argv[i]), close_input = 2;
      else if (has_suffix (argv[i], ".gz"))
	input = read_pipe ("gunzip -c %s", argv[i]), close_input = 2;
      else input = fopen (argv[i], "r"), close_input = 1;
      if (!input)
	die ("can not open and read DIMACS file '%s'", argv[i]);
      input_name = argv[i];
    }
  }
  if (!input) input_name = "<stdin>", input = stdin;
  msg ("CaDiCaL Radically Simplified CDCL Solver Version " VERSION);
  msg ("");
  msg ("reading DIMACS file from '%s'", input_name);
  if (proof) msg ("writing DRAT proof to '%s'", proof_name);
  else msg ("will not generate nor write DRAT proof");
  if (close_input == 1) fclose (input);
  if (close_input == 2) pclose (input);
  parse_dimacs ();
  res = solve ();
  if (close_proof) fclose (proof);
  reset ();
  print_statistics ();
  msg ("exit %d", res);
  return res;
}
