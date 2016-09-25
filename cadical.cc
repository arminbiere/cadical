/*--------------------------------------------------------------------------

CaDiCaL

Radically Simplified Conflict Driven Clause Learning (CDCL) SAT Solver

The goal of CaDiCal is to have a minimalistic CDCL solver, which is easy to
understand and change, while at the same time not too much slower than state
of the art CDCL solvers if pre-processing is disabled.

MIT License

Copyright (c) 2016 Armin Biere, JKU.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to
deal in the Software without restriction, including without limitation the
rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
IN THE SOFTWARE.

--------------------------------------------------------------------------*/

#define OPTIONS \
/*  NAME,                TYPE, VAL,LOW,HIGH,DESCRIPTION */ \
OPTION(bump,             bool,   1, 0,  1, "bump variables") \
OPTION(copying,          bool,   1, 0,  1, "use copying garbage collector") \
OPTION(emagluefast,    double,4e-2, 0,  1, "alpha fast learned glue") \
OPTION(emaf1,          double,1e-3, 0,  1, "alpha learned unit frequency") \
OPTION(emaf1lim,       double,   1, 0,100, "alpha unit frequency limit") \
OPTION(emainitsmoothly,  bool,   1, 0,  1, "initialize EMAs smoothly") \
OPTION(emajump,        double,1e-6, 0,  1, "alpha jump") \
OPTION(emaresolved,    double,1e-6, 0,  1, "alpha resolved glue & size") \
OPTION(ematrail,       double,1e-5, 0,  1, "alpha trail") \
OPTION(highproperdec,     int,   0, 0,1e9, "high bump per conflict limit") \
OPTION(keepglue,          int,   2, 1,1e9, "glue kept learned clauses") \
OPTION(keepsize,          int,   3, 2,1e9, "size kept learned clauses") \
OPTION(minimize,         bool,   1, 0,  1, "minimize learned clauses") \
OPTION(minimizedepth,     int,1000, 0,1e9, "recursive minimization depth") \
OPTION(minimizerecursive,bool,   1, 0,  1, "use recursive minimization") \
OPTION(quiet,            bool,   0, 0,  1, "disable all messages") \
OPTION(reduce,           bool,   1, 0,  1, "garbage collect clauses") \
OPTION(reducedynamic,    bool,   0, 0,  1, "dynamic glue & size limit") \
OPTION(reducefocus,      bool,   1, 0,  1, "keep resolved longer") \
OPTION(reducefocusglue,   int, 1e6, 0,1e9, "reduce focus max glue") \
OPTION(reducefocusize,    int, 1e6, 0,1e9, "reduce focus max size") \
OPTION(reduceglue,       bool,   1, 0,  1, "reduce by glue first") \
OPTION(reduceinc,         int, 300, 1,1e9, "reduce limit increment") \
OPTION(reduceinit,        int,2000, 0,1e9, "initial reduce limit") \
OPTION(reduceresolved,    int, 1.0, 0,  1, "resolved keep ratio") \
OPTION(reducetrail,       int,   2, 0,  2, "bump based on trail (2=both)") \
OPTION(trailweight,    double,   2, 0,1e9, "trail weight versus bump") \
OPTION(restart,          bool,   1, 0,  1, "enable restarting") \
OPTION(restartblock,   double, 1.4, 0, 10, "restart blocking factor (R)") \
OPTION(restartblocking,  bool,   1, 0,  1, "enable restart blocking") \
OPTION(restartblocklimit, int, 1e4, 0,1e9, "restart blocking limit") \
OPTION(restartblockmargin,double,1.2,0,10, "restart blocking margin") \
OPTION(restartdelay,   double, 0.5, 0,  2, "delay restart level limit") \
OPTION(restartdelaying,  bool,   0, 0,  1, "enable restart delaying") \
OPTION(restartemaf1,     bool,   1, 0,  1, "unit frequency based restart") \
OPTION(restartint,        int,  10, 1,1e9, "restart base interval") \
OPTION(restartmargin,  double, 1.1, 0, 10, "restart slow fast margin (1/K)") \
OPTION(reusetrail,       bool,   1, 0,  1, "enable trail reuse") \
OPTION(reverse,          bool,   0, 0,  1, "last index first initially") \
OPTION(verbose,          bool,   0, 0,  1, "more verbose messages") \
OPTION(witness,          bool,   1, 0,  1, "print witness") \

/*------------------------------------------------------------------------*/

// Standard C includes

#include <cassert>
#include <cctype>
#include <climits>
#include <csignal>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>

// Low-level but Posix / Unix includes

extern "C" {
#include <sys/resource.h>
#include <sys/time.h>
};

// Some standard C++ includes from STL

#include <algorithm>
#include <vector>

using namespace std;

// Configuration file for tracking version and compiler options

#include "config.h"

/*------------------------------------------------------------------------*/

// Options are defined above and statically allocated and initialized here.

static struct {
#define OPTION(N,T,V,L,H,D) \
  T N;
  OPTIONS
#undef OPTION
} opts = {
#define OPTION(N,T,V,L,H,D) \
  (T)(V),
  OPTIONS
#undef OPTION
};

/*------------------------------------------------------------------------*/

// Memory allocator for compact ordered allocation of clauses with 32-bit
// references instead of 64-bit pointers.  A similar technique is used in
// MiniSAT and descendants as well as in Splatz.  This first gives fast
// consecutive (that is cache friendly) allocation of clauses and more
// importantly allows to mix (32-bit) blocking literals with clause
// references which reduces watcher size by 2 from 16 to 8 bytes.

typedef unsigned Ref;

#ifndef ALIGNMENT
#define ALIGNMENT 4
#endif

static const size_t alignment = ALIGNMENT;   // memory alignment in an arena
#ifndef NDEBUG
static bool aligned (size_t bytes) { return !((alignment-1)&bytes); }
static bool aligned (void * ptr) { return aligned ((size_t) ptr); }
#endif

class Arena {
  char * start, * top, * end;
  void init () { start = top = end = 0; }
public:
  void enlarge (size_t new_capacity);
  size_t size () const { return top - start; }
  size_t capacity () const { return end - start; }

  void resize (char * new_top) {
    assert (start <= new_top);
    assert (new_top <= end);
    assert (aligned (new_top));
    top = new_top;
  }

  bool contains (void * ptr) const { return start <= ptr && ptr < top; }

  void * ref2ptr (Ref ref) const {
    if (!ref) return 0;
    assert (ref < size ());
    char * res = start + alignment * (size_t) ref;
    assert (contains (res));
    return res;
  }

  Ref ptr2ref (void * p) const {
    if (!p) return 0u;
    assert (contains (p)),
    assert (aligned (p));
    assert (start < p);
    return (((char*)p) - start)/alignment;
  }

  void * allocate (size_t bytes, Ref & ref);

  void release ();

  void release_and_take_over_memory (Arena & other) {
    release ();
    start = other.start, top = other.top, end = other.end;
    other.start = other.top = other.end = 0;
  }

  Arena () { init (); }
  ~Arena () { release (); }
};

/*------------------------------------------------------------------------*/

static const int    LD_MAX_GLUE     =  28;
static const int    MAX_GLUE        =  (1 << LD_MAX_GLUE);
static const size_t EXTENDED_OFFSET = sizeof(long);

struct Clause {

  unsigned redundant:1; // aka 'learned' so not 'irredundant' (original)
  unsigned garbage  :1; // can be garbage collected unless it is a 'reason'
  unsigned reason   :1; // reason / antecedent clause can not be collected
  unsigned extended :1; // see discussion on 'additional fields' below.

  unsigned glue : LD_MAX_GLUE;

  int size;             // actual size of 'literals' (at least 2)

  int literals[2];      // actually of variadic 'size' in general
                        // for binary embedded reason clauses 'size == 2'

  void set_literals (int a, int b) {
    redundant = garbage = reason = false;
    size = 2, literals[0] = a, literals[1] = b;
  }

  enum {
    RESOLVED_OFFSET = 1*sizeof(int), // of 'resolved' field before clause
  };

  // Actually, a redundant large clause has one additional field
  //
  //  long resolved;     // conflict index when last resolved
  //
  // This is however placed before the actual clause data and thus not
  // directly visible.  We set 'extended' to 'true' if this field is
  // allocated.  The policy used to determine whether a redundant clause is
  // extended uses the 'keepsize' option.  A redundant clause larger than
  // its value is extended. Usually we always keep clauses of size 2 or 3,
  // which then do not require 'resolved' fields.

  long & resolved () {
    assert (this), assert (extended);
    return *(long*) (((char*)this) - EXTENDED_OFFSET);
  }

  size_t bytes () const;
};

static Arena arena;             // memory arena for storing clauses

static inline
Clause * ref2clause (Ref r) { return (Clause*) arena.ref2ptr (r); }

static inline Ref clause2ref (Clause * c) { return arena.ptr2ref (c); }

class Reason {

  enum Tag {
    INVALID    = 0,
    EMBEDDED   = 1,
    REFERENCED = 2,
  };

  Tag tag;
  Ref ref;
  Clause embedded;

public:

  Reason () : tag (INVALID) { }

  Reason (Clause * c) : tag (REFERENCED) { ref = clause2ref (c); }

  Reason (int a, int b) : tag (EMBEDDED) { embedded.set_literals (a, b); }

  bool referenced () const { return tag == REFERENCED; }

  Ref reference () { return ref; }

  void update_reference (Ref r) { assert (referenced ()), ref = r; }

  Clause * clause () {
         if (!tag)              return 0;
    else if (tag == REFERENCED) return ref2clause (ref);
    else                        return &embedded;
  }

  Clause * operator -> () { return clause (); }
  operator bool () { return tag; }
};

struct NoReason : public Reason { };
struct UnitReason : public Reason { };
struct DecisionReason : public Reason { };

/*------------------------------------------------------------------------*/

struct Var {

  int level;            // decision level
  int trail;            // trail level

  bool seen;            // analyzed in 'analyze' and will be bumped
  bool poison;          // can not be removed during clause minimization
  bool removable;       // can be removed during clause minimization
  int mark;             // reason position for non-recursive DFS

  int prev, next;       // double links for decision VMTF queue
  long bumped;          // enqueue time stamp for VMTF queue

  Reason reason;        // implication graph edge

  Var () :
    seen (false), poison (false), removable (false), mark (0),
    prev (0), next (0), bumped (0)
  { }
};

struct Watch {
  int blit;             // if blocking literal is true do not visit clause
  Ref ref;
  Watch (int b, Ref r) : blit (b), ref (r) { }
  Watch () { }
};

typedef vector<Watch> Watches;          // of one literal

struct Level {
  int decision;         // decision literal of level
  int seen;             // how man variables seen during 'analyze'
  int trail;            // smallest trail position seen
  void reset () { seen = 0, trail = INT_MAX; }
  Level (int d) : decision (d) { reset (); }
  Level () { }
};

/*------------------------------------------------------------------------*/

// We have a more complex generic exponential moving average struct here
// for more robust initialization (see comments before 'update' below).

struct EMA {
  double value;         // current average value
  double alpha;         // percentage contribution of new values
  double beta;          // current upper approximation of alpha
  long wait;            // count-down using 'beta' instead of 'alpha'
  long period;          // length of current waiting phase
  EMA (double a = 0) :
     value (0), alpha (a), wait (0), period (0)
  {
    assert (0 <= alpha), assert (alpha <= 1);
    beta = opts.emainitsmoothly ? 1.0 : alpha;
  }
  operator double () const { return value; }
  void update (double y, const char * name);
};

struct AVG {
  double value;
  long count;
  AVG () : value (0), count (0) { }
  operator double () const { return value; }
  void update (double y, const char * name);
};

#ifdef PROFILING        // enabled by './configure -p'

struct Timer {
  double started;       // starting time (in seconds) for this phase
  double * profile;     // update this profile if phase stops
  Timer (double s, double * p) : started (s), profile (p) { }
  Timer () { }
  void update (double now) { *profile += now - started; started = now; }
};

#endif

/*------------------------------------------------------------------------*/

// Static variables

static int max_var, num_original_clauses;
static int min_lit, max_lit;

#ifndef NDEBUG
static vector<int> original_literals;
#endif

static Var * vars;

static signed char * vals;              // assignment
static signed char * phases;            // saved previous assignment

// This 'others' table contains for each literal a zero terminated sequence
// of other literals in binary clauses with the first literal.  This avoids
// to use 'vector' for this data which is mostly static.  New binary clauses
// are treated as long clauses until the next 'reduce' after which this
// binary data structure is updated.

static int * others;
static size_t size_others;

static struct {
  Watches * watches;
  int ** binaries;              // points to start of sequence.
} literal;

// VMTF decision queue

static struct {
  int first, last;      // anchors (head/tail) for doubly linked list
  int assigned;         // all variables after this one are assigned
} queue;

static bool unsat;              // empty clause found or learned

static int level;               // decision level (levels.size () - 1)
static vector<Level> levels;

static vector<int> trail;       // assigned literals

static struct {
  size_t watches;       // next literal position for watches
  size_t binaries;      // next literal position for binaries
} next;                 // as BFS indices into 'trail' for propagation

static vector<int> clause;      // temporary clause in parsing & learning
static vector<Ref> clauses;     // references to all clauses
static bool iterating;          // report top-level assigned variables

static struct {
  vector<int> literals;         // seen & bumped literals in 'analyze'
  vector<int> levels;           // decision levels of 1st UIP clause
  vector<int> minimized;        // marked removable or poison in 'minmize'
} seen;

static vector<Clause*> resolved;  // large clauses in 'analyze'
static Reason conflict;           // set: 'propagation', reset: 'analyze'
static bool clashing_unit;        // set: 'parse_dimacs'

static struct {
  long conflicts;
  long decisions;
  long propagations;            // propagated literals in 'propagate'

  struct {
    long count;
    long tried;
    long delayed;
    long blocked;
    long unforced;
    long forced;
    long reused;
    long unit;
  } restart;

  long reports, sections;

  long bumped;                  // seen and bumped variables in 'analyze'
  long resolved;                // resolved redundant clauses in 'analyze'
  long searched;                // searched decisions in 'decide'

  long trailsorted;             // trail sorted before bumping

  struct { long count, clauses, bytes; } reduce; // in 'reduce'

  struct { long learned, minimized; } literals;  // in 'minimize_clause'

  struct { long redundant, irredundant, current, max; } clauses;
  struct { struct { size_t current, max; } total, watcher; } bytes;

  struct { long unit, binary; } learned;

  int fixed;                    // top level assigned variables
} stats;

#ifdef PROFILING
static vector<Timer> timers;
#endif

// Averages to control which clauses are collected in 'reduce' and when to
// force and delay 'restart' respectively.  Most of them are exponential
// moving average, but for the slow glue we use an actual average.

static struct {
  struct { EMA unit; } frequency;
  struct { EMA glue, size; } resolved;
  struct { EMA fast; AVG slow, blocking, nonblocking; } glue;
  EMA jump, trail;
} avg;

static struct {
  bool enabled, exploring;
  long limit, inc;
} blocking;

// Limits for next restart, reduce.

static struct {
  struct { long conflicts, resolved; int fixed; } reduce;
  struct { long conflicts; } restart;
} limits;

// Increments for next restart, reduce interval.

static struct {
  struct { long conflicts; } reduce;
  double unit, binary;
} inc;

static FILE * input_file, * dimacs_file, * proof_file;
static const char *input_name, *dimacs_name, *proof_name;
static int lineno, close_input, close_proof, trace_proof;

#ifndef NDEBUG

// Sam Buss suggested to debug the case where a solver incorrectly claims
// the formula to be unsatisfiable by checking every learned clause to be
// satisfied by a satisfying assignment.  Thus the first inconsistent
// learned clause will be immediately flagged without the need to generate
// proof traces and perform forward proof checking.  The incorrectly derived
// clause will raise an abort signal and thus allows to debug the issue with
// a symbolic debugger immediately.

static FILE * solution_file;
static const char *solution_name;
static signed char * solution;          // like 'vals' (and 'phases')

#endif

/*------------------------------------------------------------------------*/

// Signal handlers for printing statistics even if solver is interrupted.

static bool catchedsig = false;

#define SIGNALS \
SIGNAL(SIGINT) \
SIGNAL(SIGSEGV) \
SIGNAL(SIGABRT) \
SIGNAL(SIGTERM) \
SIGNAL(SIGBUS) \

#define SIGNAL(SIG) \
static void (*SIG ## _handler)(int);
SIGNALS
#undef SIGNAL

/*------------------------------------------------------------------------*/

static void msg (const char * fmt, ...) {
  va_list ap;
  if (opts.quiet) return;
  fputs ("c ", stdout);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void section (const char * title) {
  if (opts.quiet) return;
  char line[160];
  sprintf (line, "---- [ %s ] ", title);
  assert (strlen (line) < sizeof line);
  int i = 0;
  for (i = strlen (line); i < 76; i++) line[i] = '-';
  line[i] = 0;
  if (stats.sections++) msg ("");
  msg (line);
  msg ("");
}

static void die (const char * fmt, ...) {
  va_list ap;
  fputs ("*** cadical error: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void perr (const char * fmt, ...) {
  va_list ap;
  fprintf (stderr, "%s:%d: parse error: ", input_name, lineno);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

/*------------------------------------------------------------------------*/

// You might want to turn on logging with './configure -l'.

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
    if (!c->redundant) printf (" irredundant");
    else if (c->extended)
      printf (" redundant glue %u resolved %ld", c->glue, c->resolved ());
    else printf (" redundant without glue");
    printf (" size %d clause", c->size);
    for (int i = 0; i < c->size; i++)
      printf (" %d", c->literals[i]);
  } else if (level) printf (" decision");
  else printf (" unit");
  fputc ('\n', stdout);
  fflush (stdout);
}

static void LOG (const vector<int> & clause, const char *fmt, ...) {
  va_list ap;
  printf ("c LOG %d ", level);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  for (size_t i = 0; i < clause.size (); i++)
    printf (" %d", clause[i]);
  fputc ('\n', stdout);
  fflush (stdout);
}

#else
#define LOG(ARGS...) do { } while (0)
#endif

/*------------------------------------------------------------------------*/

static double relative (double a, double b) { return b ? a / b : 0; }

static double percent (double a, double b) { return relative (100 * a, b); }

static double seconds () {
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;  // user time
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec; // + system time
  return res;
}

static void inc_bytes (size_t bytes) {
  if ((stats.bytes.total.current += bytes) > stats.bytes.total.max)
    stats.bytes.total.max = stats.bytes.total.current;
}

static void dec_bytes (size_t bytes) {
  assert (stats.bytes.total.current >= bytes);
  stats.bytes.total.current -= bytes;
}

static inline size_t align (size_t bytes) {
  size_t res = (bytes + (alignment-1)) & ~ (alignment-1);
  assert (aligned (res)), assert (!aligned (bytes) || bytes == res);
  return res;
}

inline void Arena::release () {
  if (!start) return;
  dec_bytes (capacity ());
  delete [] start;
  init ();
}

inline void * Arena::allocate (size_t bytes, Ref & ref) {
  bytes = align (bytes);
  char * new_top = top + bytes;
  if (new_top > end) enlarge (new_top - start), new_top = top + bytes;
  char * res = top;
  top = new_top;
  ref = (res - start)/alignment;
  assert (start + alignment * (size_t) ref == res);
  assert (ref2ptr (ref) == res);
  assert (aligned (res)), assert (contains (res));
  return res;
}

void Arena::enlarge (size_t requested_capacity) {
  if (!start) requested_capacity += alignment;          // zero ref = zero ptr
  if (requested_capacity > (1l << 32))
    die ("maximum memory arena of %ld GB exhausted",
      ((alignment * (1l<<32)) >> 30));
  size_t old_capacity = capacity (), old_size = size ();
  size_t new_capacity = old_capacity ? old_capacity : 4;
  while (new_capacity < requested_capacity)
    if (new_capacity < (1l << 30)) new_capacity *= 2;
    else new_capacity += (1l << 30);
  assert (new_capacity >= requested_capacity);
  char * new_start = new char[new_capacity];
  memcpy (new_start, start, old_size);
  dec_bytes (old_capacity);
  inc_bytes (new_capacity);
  if (start) delete [] start;
  start = new_start;
  top   = new_start + (old_size ? old_size : alignment);
  end   = new_start + new_capacity;
  LOG ("enlarged arena to new capacity %ld", new_capacity);
}

#define VECTOR_BYTES(V) \
  res += V.capacity () * sizeof (V[0])

static size_t vector_bytes () {
  size_t res = 0;
#ifndef NDEBUG
  VECTOR_BYTES (original_literals);
#endif
  VECTOR_BYTES (clause);
  VECTOR_BYTES (trail);
  VECTOR_BYTES (seen.literals);
  VECTOR_BYTES (seen.levels);
  VECTOR_BYTES (seen.minimized);
  VECTOR_BYTES (resolved);
  VECTOR_BYTES (clauses);
  VECTOR_BYTES (levels);
  return res;
}

static size_t max_bytes () {
  size_t res = stats.bytes.total.max + vector_bytes ();
  if (stats.bytes.watcher.max > 0) res += stats.bytes.watcher.max;
  else res += (4 * stats.clauses.max * sizeof (Watch)) / 3;
  return res;
}

static size_t current_bytes () {
  size_t res = stats.bytes.total.current + vector_bytes ();
  if (stats.bytes.watcher.current > 0) res += stats.bytes.watcher.current;
  else res += (4 * stats.clauses.current * sizeof (Watch)) / 3;
  return res;
}

static int active_variables () { return max_var - stats.fixed; }

/*------------------------------------------------------------------------*/

// Faster file IO without locking.

static void print (char ch, FILE * file = stdout) {
  fputc_unlocked (ch, file);
}

static void print (const char * s, FILE * file = stdout) {
  fputs_unlocked (s, file);
}

static void print (int lit, FILE * file = stdout) {
  char buffer[20];
  sprintf (buffer, "%d", lit);
  print (buffer, file);
}

/*------------------------------------------------------------------------*/

// The following statistics are printed in columns, whenever 'report' is
// called.  For instance 'reduce' with prefix '-' will call it.  The other
// more interesting report is due to learning a unit, called iteration, with
// prefix 'i'.  To add another statistics column, add a corresponding line
// here.  If you want to report something else add 'report (..)' functions.

#define REPORTS \
/*     HEADER, PRECISION, MIN, VALUE */ \
REPORT("seconds",      2, 5, seconds ()) \
REPORT("MB",           0, 2, current_bytes () / (double)(1l<<20)) \
REPORT("level",        1, 4, avg.jump) \
REPORT("f1",           0, 2, 10.0 * avg.frequency.unit) \
REPORT("reductions",   0, 2, stats.reduce.count) \
REPORT("restarts",     0, 4, stats.restart.count) \
REPORT("conflicts",    0, 5, stats.conflicts) \
REPORT("redundant",    0, 5, stats.clauses.redundant) \
REPORT("glue",         1, 4, avg.glue.slow) \
REPORT("fastglue",     1, 4, avg.glue.fast) \
REPORT("irredundant",  0, 4, stats.clauses.irredundant) \
REPORT("variables",    0, 4, active_variables ()) \
REPORT("remaining",   -1, 5, percent (active_variables (), max_var)) \
REPORT("properdec",    0, 3, relative (stats.propagations, stats.decisions)) \
REPORT("trail",        1, 4, avg.trail) \
REPORT("resglue",      1, 4, avg.resolved.glue) \
REPORT("ressize",      1, 4, avg.resolved.size) \

struct Report {
  const char * header;
  char buffer[20];
  int pos;
  Report (const char * h, int precision, int min, double value) : header (h) {
    char fmt[10];
    sprintf (fmt, "%%.%df", abs (precision));
    if (precision < 0) strcat (fmt, "%%");
    sprintf (buffer, fmt, value);
    const int min_width = min;
    if (strlen (buffer) >= (size_t) min_width) return;
    sprintf (fmt, "%%%d.%df", min_width, abs (precision));
    if (precision < 0) strcat (fmt, "%%");
    sprintf (buffer, fmt, value);
  }
  Report () { }
  void print_header (char * line) {
    int len = strlen (header);
    for (int i = -1, j = pos - (len + 1)/2 - 1; i < len; i++, j++)
      line[j] = i < 0 ? ' ' : header[i];
  }
};

static void report (char type, bool verbose = false) {
  if (opts.quiet || (verbose && !opts.verbose)) return;
  const int max_reports = 32;
  Report reports[max_reports];
  int n = 0;
#define REPORT(HEAD,PREC,MIN,EXPR) \
  assert (n < max_reports); \
  reports[n++] = Report (HEAD, PREC, MIN, (double)(EXPR));
  REPORTS
#undef REPORT
  if (!(stats.reports++ % 20)) {
    print ("c\n", stdout);
    int pos = 4;
    for (int i = 0; i < n; i++) {
      int len = strlen (reports[i].buffer);
      reports[i].pos = pos + (len + 1)/2;
      pos += len + 1;
    }
    const int max_line = pos + 20, nrows = 3;
    char line[max_line];
    for (int start = 0; start < nrows; start++) {
      int i;
      for (i = 0; i < max_line; i++) line[i] = ' ';
      line[0] = 'c';
      for (i = start; i < n; i += nrows) reports[i].print_header (line);
      for (i = max_line-1; line[i-1] == ' '; i--) ;
      line[i] = 0;
      print (line, stdout);
      print ('\n', stdout);
    }
    print ("c\n", stdout);
  }
  print ("c "), print (type);
  for (int i = 0; i < n; i++)
    print (' '), print (reports[i].buffer);
  print ('\n', stdout);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/

// You might want to turn on profiling with './configure -p'.

#ifdef PROFILING

static void start (double * p) { timers.push_back (Timer (seconds (), p)); }

static void stop (double * p) {
  assert (!timers.empty ());
  Timer & t = timers.back ();
  assert (p == t.profile), (void) p;
  t.update (seconds ());
  timers.pop_back ();
}

// To profile say 'foo', just add another line 'PROFILE(foo)' and wrap
// the code to be profiled within a 'START (foo)' / 'STOP (foo)' block.

#define PROFILES \
PROFILE(analyze) \
PROFILE(bump) \
PROFILE(decide) \
PROFILE(minimize) \
PROFILE(parse) \
PROFILE(propagate) \
PROFILE(reduce) \
PROFILE(restart) \
PROFILE(search) \

static struct {
#define PROFILE(NAME) \
  double NAME;
  PROFILES
#undef PROFILE
} profile;

#define START(P) start (&profile.P)
#define STOP(P) stop (&profile.P)

static void update_all_timers (double now) {
  for (size_t i = 0; i < timers.size (); i++) timers[i].update (now);
}

static void print_profile (double now) {
  update_all_timers (now);
  section ("run-time profiling data");
  const size_t size = sizeof profile / sizeof (double);
  struct { double value; const char * name; } profs[size];
  size_t i = 0;
#define PROFILE(NAME) \
  profs[i].value = profile.NAME; \
  profs[i].name = # NAME; \
  i++;
  PROFILES
#undef PROFILE
  assert (i == size);
  // Explicit bubble sort to avoid heap allocation since 'print_profile'
  // is also called during catching a signal after out of heap memory.
  // This only makes sense if 'profs' is allocated on the stack, and
  // not the heap, which should be the case.
  for (i = 0; i < size; i++) {
    for (size_t j = i + 1; j < size; j++)
      if (profs[j].value > profs[i].value)
        swap (profs[i].value, profs[j].value),
        swap (profs[i].name, profs[j].name);
    msg ("%12.2f %7.2f%% %s",
      profs[i].value, percent (profs[i].value, now), profs[i].name);
  }
  msg ("  ===============================");
  msg ("%12.2f %7.2f%% all", now, 100.0);
}

#else
#define START(ARGS...) do { } while (0)
#define STOP(ARGS...) do { } while (0)
#define print_profile(ARGS...) do { } while (0)
#endif

/*------------------------------------------------------------------------*/

// Updating an exponential moving average is placed here since we want to
// log both updates and phases of initialization, thus need 'LOG'.

inline void EMA::update (double y, const char * name) {

  // This is the common exponential moving average update.

  value += beta * (y - value);
  LOG ("update %s EMA with %g beta %g yields %g", name, y, beta, value);

  if (!opts.emainitsmoothly) return;

  // However, we used the upper approximation 'beta' of 'alpha'.  The idea
  // is that 'beta' slowly moves down to 'alpha' to smoothly initialize
  // the exponential moving average.  This technique was used in 'Splatz'.

  // We maintain 'beta = 2^-period' until 'beta < alpha' and then set it to
  // 'alpha'.  The period gives the number of updates this 'beta' is used.
  // So for smaller and smaller 'beta' we wait exponentially longer until
  // 'beta' is halfed again.  The sequence of 'beta's is
  //
  //   1,
  //   1/2, 1/2,
  //   1/4, 1/4, 1/4, 1/4
  //   1/8, 1/8, 1/8, 1/8, 1/8, 1/8, 1/8, 1/8,
  //   ...
  //
  //  We did not derive this formally, but observed it during logging.  This
  //  is in 'Splatz' but not published yet, e.g., was not in POS'15.

  if (beta <= alpha || wait--) return;
  wait = period = 2*(period + 1) - 1;
  beta *= 0.5;
  if (beta < alpha) beta = alpha;
  LOG ("new %s EMA wait = period = %ld, beta = %g", name, wait, beta);
}

inline void AVG::update (double y, const char * name) {
  value = count * value + y;
  value /= ++count;
  LOG ("update %s AVG with %g yields %g", name, y, value);
}

// Short hand for better logging.

#define UPDATE(EMA_OR_AVG,Y) EMA_OR_AVG.update ((Y), #EMA_OR_AVG)

/*------------------------------------------------------------------------*/

// In essence 'abs' but also checks whether 'lit' is a valid literal.

static int vidx (int lit) {
  int idx;
  assert (lit), assert (lit != INT_MIN);
  idx = abs (lit);
  assert (idx <= max_var);
  return idx;
}

// Get the value of a literal: -1 = false, 0 = unassigned, 1 = true.

static inline int val (int lit) {
  int idx = vidx (lit), res = vals[idx];
  if (lit < 0) res = -res;
  return res;
}

// As 'val' but restricted to the root-level value of a literal.

static inline int fixed (int lit) {
  int idx = vidx (lit), res = vals[idx];
  if (res && vars[idx].level) res = 0;
  if (lit < 0) res = -res;
  return res;
}

// Sign of an integer, but also does proper index checking.

static inline int sign (int lit) {
  assert (lit), assert (abs (lit) <= max_var);
  return lit < 0 ? -1 : 1;
}

// Unsigned version with LSB denoting sign.  This is used in indexing arrays
// by literals.  The idea is to keep the elements in such an array for both
// the positive and negated version of a literal close together

static inline unsigned vlit (int lit) {
  return (lit < 0) + 2u * (unsigned) vidx (lit);
}

static inline Watches & watches (int lit) {
  return literal.watches[vlit (lit)];
}

static inline int * & binaries (int lit) {
  return literal.binaries[vlit (lit)];
}

static inline Var & var (int lit) { return vars [vidx (lit)]; }

/*------------------------------------------------------------------------*/

// Very expensive check for the consistency of the VMTF queue.

static void check_vmtf_queue_invariant () {
#if 0
  int count = 0, idx, next;
  for (idx = queue.first; idx; idx = var (idx).next) count++;
  assert (count == max_var);
  for (idx = queue.last; idx; idx = var (idx).prev) count--;
  assert (!count);
  for (idx = queue.first; idx && (next = var (idx).next); idx = next)
    assert (var (idx).bumped < var (next).bumped);
  for (idx = queue.assigned; idx && (next = var (idx).next); idx = next)
    assert (val (next));
#endif
}

/*------------------------------------------------------------------------*/

static void trace_empty_clause () {
  if (!proof_file) return;
  LOG ("tracing empty clause");
  print ("0\n", proof_file);
}

static void trace_unit_clause (int unit) {
  if (!proof_file) return;
  LOG ("tracing unit clause %d", unit);
  print (unit, proof_file);
  print (" 0\n", proof_file);
}

static void trace_clause (Clause * c, bool add) {
  if (!proof_file) return;
  LOG (c, "tracing %s", add ? "addition" : "deletion");
  if (!add) print ("d ", proof_file);
  const int size = c->size, * lits = c->literals;
  for (int i = 0; i < size; i++)
    print (lits[i], proof_file), print (" ", proof_file);
  print ("0\n", proof_file);
}

static void trace_flushing_clause (Clause * c) {
  if (!proof_file) return;
  LOG (c, "tracing flushing");
  const int size = c->size, * lits = c->literals;
  for (int i = 0; i < size; i++) {
    const int lit = lits[i];
    if (fixed (lit) >= 0)
      print (lit, proof_file), print (" ", proof_file);
  }
  print ("0\nd ", proof_file);
  for (int i = 0; i < size; i++)
    print (lits[i], proof_file), print (" ", proof_file);
  print ("0\n", proof_file);
}

static void trace_add_clause (Clause * c) { trace_clause (c, true); }

static void trace_delete_clause (Clause * c) { trace_clause (c, false); }

static void learn_empty_clause () {
  assert (!unsat);
  LOG ("learned empty clause");
  trace_empty_clause ();
  unsat = true;
}

static void learn_unit_clause (int lit) {
  LOG ("learned unit clause %d", lit);
  trace_unit_clause (lit);
  iterating = true;
  stats.fixed++;
}

/*------------------------------------------------------------------------*/

static void assign (int lit, Reason reason) {
  int idx = vidx (lit);
  assert (!vals[idx]);
  Var & v = vars[idx];
  if (!(v.level = level)) learn_unit_clause (lit);
  v.reason = reason;
  vals[idx] = phases[idx] = sign (lit);
  assert (val (lit) > 0);
  v.trail = (int) trail.size ();
  trail.push_back (lit);
  LOG (reason.clause (), "assign %d", lit);
}

static void unassign (int lit) {
  assert (val (lit) > 0);
  int idx = vidx (lit);
  vals[idx] = 0;
  LOG ("unassign %d", lit);
  Var * v = vars + idx;
  if (var (queue.assigned).bumped >= v->bumped) return;
  queue.assigned = idx;
  LOG ("queue next moved to %d", idx);
  check_vmtf_queue_invariant ();
}

static void backtrack (int target_level = 0) {
  assert (target_level <= level);
  if (target_level == level) return;
  LOG ("backtracking to decision level %d", target_level);
  int decision = levels[target_level + 1].decision, lit;
  do {
    unassign (lit = trail.back ());
    trail.pop_back ();
  } while (lit != decision);
  if (trail.size () < next.watches) next.watches = trail.size ();
  if (trail.size () < next.binaries) next.binaries = trail.size ();
  levels.resize (target_level + 1);
  level = target_level;
}

/*------------------------------------------------------------------------*/

static void watch_literal (int lit, int blit, Clause * c) {
  watches (lit).push_back (Watch (blit, clause2ref (c)));
  LOG (c, "watch %d blit %d in", lit, blit);
}

static void watch_clause (Clause * c) {
  assert (c->size > 1);
  int l0 = c->literals[0], l1 = c->literals[1];
  watch_literal (l0, l1, c);
  watch_literal (l1, l0, c);
}

inline size_t Clause::bytes () const {
  size_t res = sizeof *this + (size - 2) * sizeof (int);
  if (extended) res += EXTENDED_OFFSET;
  return res;
}

static Clause * new_clause (bool red, unsigned glue = 0) {
  assert (clause.size () <= (size_t) INT_MAX);
  const int size = (int) clause.size ();  assert (size >= 2);
  size_t bytes = sizeof (Clause) + (size - 2) * sizeof (int);
  const bool extended = red && size > opts.keepsize;
  if (extended) bytes += EXTENDED_OFFSET;
  Ref ref;
  char * ptr = (char*) arena.allocate (bytes, ref);
  if (extended) ptr += EXTENDED_OFFSET, ref += EXTENDED_OFFSET/alignment;
  Clause * res = (Clause*) ptr;
  res->redundant = red;
  res->garbage = false;
  res->reason = false;
  res->extended = extended;
  res->glue = min ((unsigned) MAX_GLUE, glue);
  res->size = size;
  for (int i = 0; i < size; i++) res->literals[i] = clause[i];
  if (extended) res->resolved () = ++stats.resolved;
  assert (res->bytes () == bytes);
  clauses.push_back (ref);
  if (red) stats.clauses.redundant++;
  else     stats.clauses.irredundant++;
  if (++stats.clauses.current > stats.clauses.max)
    stats.clauses.max = stats.clauses.current;
  LOG (res, "new");
  return res;
}

struct lit_less_than {
  bool operator () (int a, int b) {
    int s = abs (a), t = abs (b);
    return s < t || (s == t && a < b);
  }
};

static bool tautological () {
  sort (clause.begin (), clause.end (), lit_less_than ());
  size_t j = 0;
  int prev = 0;
  for (size_t i = 0; i < clause.size (); i++) {
    int lit = clause[i];
    if (lit == -prev) return true;
    if (lit !=  prev) clause[j++] = lit;
  }
  if (j < clause.size ()) {
    clause.resize (j);
    LOG ("removed %d duplicates", clause.size () - j);
  }
  return false;
}

static void add_new_original_clause () {
  int size = (int) clause.size ();
  if (!size) {
    if (!unsat) msg ("original empty clause"), unsat = true;
    else LOG ("original empty clause produces another inconsistency");
  } else if (size == 1) {
    int unit = clause[0], tmp = val (unit);
    if (!tmp) assign (unit, UnitReason ());
    else if (tmp < 0) {
      if (!unsat) msg ("parsed clashing unit"), clashing_unit = true;
      else LOG ("original clashing unit produces another inconsistency");
    } else LOG ("original redundant unit");
  } else watch_clause (new_clause (false));
}

static Clause * new_learned_clause (int glue) {
  Clause * res = new_clause (true, glue);
  trace_add_clause (res);
  watch_clause (res);
  return res;
}

/*------------------------------------------------------------------------*/

// The 'propagate' function is usually the hot-spot of a CDCL SAT solver.
// The 'trail' stack saves assigned variables and is used here as BFS queue
// for checking clauses with the negation of assigned variables for being in
// conflict or whether they produce additional assignments (units).  This
// version of 'propagate' uses lazy watches and keeps two watches literals
// at the beginning of the clause.  We also have seperate data structures
// for binary clauses and use 'blocking literals' to reduce the number of
// times clauses have to be visited.

static bool propagate () {
  assert (!unsat);
  START (propagate);

  // The number of assigned variables propagated (at least for binary
  // clauses) gives the number of 'propagations', which is commonly used
  // to compare raw 'propagation speed' of solvers.  We save the BFS next
  // binary counter to avoid updating the 64-bit 'propagations' counter in
  // this tight loop below.

  const size_t before = next.binaries;

  while (!conflict) {

    // Propagate binary clauses eagerly and even continue propagating if a
    // conflicting binary clause is found.

    while (next.binaries < trail.size ()) {
      const int lit = trail[next.binaries++];
      LOG ("propagating binaries of %d", lit);
      assert (val (lit) > 0);
      assert (literal.binaries);
      const int * p = binaries (-lit);
      if (!p) continue;
      int other;
      while ((other = *p++)) {
        const int b = val (other);
        if (b < 0) conflict = Reason (-lit, other);
        else if (!b) assign (other, Reason (-lit, other));
      }
    }

    // Then if all binary clauses are propagated, go over longer clauses
    // with the negation of the assigned literal on the trail.

    if (!conflict && next.watches < trail.size ()) {
      const int lit = trail[next.watches++];
      assert (val (lit) > 0);
      LOG ("propagating watches of %d", lit);
      Watches & ws = watches (-lit);
      size_t i = 0, j = 0;
      while (i < ws.size ()) {
        const Watch w = ws[j++] = ws[i++];      // keep watch by default
        const int b = val (w.blit);
        if (b > 0) continue;
        Clause * c = ref2clause (w.ref);
        const int size = c->size;
        int * lits = c->literals;
        if (lits[1] != -lit) swap (lits[0], lits[1]);
        assert (lits[1] == -lit);
        const int u = val (lits[0]);
        if (u > 0) ws[j-1].blit = lits[0];
        else {
          int k, v = -1;
          for (k = 2; k < size && (v = val (lits[k])) < 0; k++)
            ;
          if (v > 0) ws[j-1].blit = lits[k];
          else if (!v) {
            LOG (c, "unwatch %d in", -lit);
            swap (lits[1], lits[k]);
            watch_literal (lits[1], -lit, c);
            j--;                                // flush watch
          } else if (!u) assign (lits[0], c);
          else { conflict = c; break; }
        }
      }
      while (i < ws.size ()) ws[j++] = ws[i++];
      ws.resize (j);

    } else break;
  }

  if (conflict) { stats.conflicts++; LOG (conflict.clause (), "conflict"); }
  stats.propagations += next.binaries - before;;

  STOP (propagate);
  return !conflict;
}

/*------------------------------------------------------------------------*/

#ifndef NDEBUG

// Like 'val' for 'vals' but 'sol' is for 'solution'.

static int sol (int lit) {
  assert (solution);
  int res = solution[vidx (lit)];
  if (lit < 0) res = -res;
  return res;
}

#endif

// See comments at the declaration of 'solution' above.  This is used
// for debugging inconsistent models and unexpected UNSAT results.

static void check_clause () {
#ifndef NDEBUG
  if (!solution) return;
  bool satisfied = false;
  for (size_t i = 0; !satisfied && i < clause.size (); i++)
    satisfied = (sol (clause[i]) > 0);
  if (satisfied) return;
  fflush (stdout);
  fputs (
    "*** cadical error: learned clause unsatisfied by solution:\n",
    stderr);
  for (size_t i = 0; i < clause.size (); i++)
    fprintf (stderr, "%d ", clause[i]);
  fputs ("0\n", stderr);
  fflush (stderr);
  abort ();
#endif
}

/*------------------------------------------------------------------------*/

// Compact recursive but bounded version of DFS for minimizing clauses.

static bool recursive_minimize_literal (int lit, int depth = 0) {
  Var & v = var (lit);
  if (!v.level || v.removable || (depth && v.seen)) return true;
  if (!v.reason || v.poison || v.level == level) return false;
  const Level & l = levels[v.level];
  if ((!depth && l.seen < 2) || v.trail <= l.trail) return false;
  if (depth > opts.minimizedepth) return false;
  const int size = v.reason->size, * lits = v.reason->literals;
  bool res = true;
  for (int i = 0, other; res && i < size; i++)
    if ((other = lits[i]) != lit)
      res = recursive_minimize_literal (-other, depth+1);
  if (res) v.removable = true; else v.poison = true;
  seen.minimized.push_back (lit);
  if (!depth) LOG ("minimizing %d %s", lit, res ? "succeeded" : "failed");
  return res;
}

// Non-recursive unbounded version of DFS for minimizing clauses.  It is
// more ugly and needs slightly more heap memory for variables due to 'mark'
// used for saving the position in the reason clause.  It also trades stack
// memory for holding the recursion stack for heap memory, which however
// should be negligible.  It runs minimization until completion though and
// thus might remove more literals than the bounded recursive version.

static int minimize_base_case (int root, int lit) {
  Var & v = var (lit);
  if (!v.level || v.removable || (root != lit && v.seen)) return 1;
  if (!v.reason || v.poison || v.level == level) return -1;
  const Level & l = levels[v.level];
  if ((root == lit && l.seen < 2) || v.trail <= l.trail) return -1;
  return 0;
}

static bool derecursived_minimize_literal (int root) {
  vector<int> stack;
  stack.push_back (root);
  while (!stack.empty ()) {
    const int lit = stack.back ();
    if (minimize_base_case (root, lit)) stack.pop_back ();
    else {
      Var & v = var (lit);
      const int size = v.reason->size, * lits = v.reason->literals;
NEXT: if (v.mark < size) {
        const int other = lits[v.mark];
        if (other == lit)   { v.mark++;        goto NEXT; }
        else {
          const int tmp = minimize_base_case (root, -other);
               if (tmp < 0) { v.poison = true; goto DONE; }
          else if (tmp > 0) { v.mark++;        goto NEXT; }
          else stack.push_back (-other);
        }
      } else {
        v.removable = true;
DONE:   seen.minimized.push_back (lit);
        stack.pop_back ();
      }
    }
  }
  const bool res = (minimize_base_case (root, root) > 0);
  LOG ("minimizing literal %d %s", root, res ? "succeeded" : "failed");
  return res;
}

static bool minimize_literal (int root) {
  if (opts.minimizerecursive) return recursive_minimize_literal (root);
  else return derecursived_minimize_literal (root);
}

struct trail_smaller_than {
  bool operator () (int a, int b) { return var (a).trail < var (b).trail; }
};

static void minimize_clause () {
  if (!opts.minimize) return;
  START (minimize);
  sort (clause.begin (), clause.end (), trail_smaller_than ());
  LOG (clause, "minimizing first UIP clause");
  assert (seen.minimized.empty ());
  stats.literals.learned += clause.size ();
  size_t j = 0;
  for (size_t i = 0; i < clause.size (); i++)
    if (minimize_literal (-clause[i])) stats.literals.minimized++;
    else clause[j++] = clause[i];
  LOG ("minimized %d literals", clause.size () - j);
  clause.resize (j);
  for (size_t i = 0; i < seen.minimized.size (); i++) {
    Var & v = var (seen.minimized[i]);
    v.removable = v.poison = false;
    v.mark = 0;
  }
  seen.minimized.clear ();
  STOP (minimize);
  check_clause ();
}

/*------------------------------------------------------------------------*/

static void dequeue (Var * v) {
  if (v->prev) var (v->prev).next = v->next; else queue.first = v->next;
  if (v->next) var (v->next).prev = v->prev; else queue.last = v->prev;
}

static void enqueue (Var * v, int idx) {
  if ((v->prev = queue.last)) var (queue.last).next = idx;
  else queue.first = idx;
  queue.last = idx;
  v->next = 0;
}

static int next_decision_variable () {
  int res;
  while (val (res = queue.assigned))
    queue.assigned = var (queue.assigned).prev, stats.searched++;
  LOG ("next decision variable %d", res);
  return res;
}

static bool high_propagations_per_decision () {
  const double r = relative (stats.propagations, stats.decisions);
  const bool res = r > opts.highproperdec;
  LOG ("%s propagation per decision rate %.2f", (res ? "high" : "low"), r);
  return res;
}

struct bumped_earlier {
  bool operator () (int a, int b) { return var (a).bumped < var (b).bumped; }
};

struct bumped_plus_trail_smaller_than {
  bool operator () (int a, int b) {
    Var & u = var (a), & v = var (b);
    return u.bumped + opts.trailweight * u.trail <
           v.bumped + opts.trailweight * v.trail;
  }
};

static void bump_and_clear_seen_variables (int uip) {
  START (bump);
  if (opts.reducetrail == 1 && high_propagations_per_decision ()) {
    LOG ("trail sorting seen variables before bumping");
    stats.trailsorted++;
    sort (seen.literals.begin (),
          seen.literals.end (),
          trail_smaller_than ());
  } else if (opts.reducetrail == 2) {
    LOG ("bumped plus trail sorting seen variables before bumping");
    sort (seen.literals.begin (),
          seen.literals.end (),
          bumped_plus_trail_smaller_than ());
  } else {
    LOG ("bumped sorting seen variables before bumping");
    sort (seen.literals.begin (),
          seen.literals.end (),
          bumped_earlier ());
  }
  if (uip < 0) uip = -uip;
  for (size_t i = 0; i < seen.literals.size (); i++) {
    int idx = vidx (seen.literals[i]);
    Var * v = vars + idx;
    assert (v->seen);
    v->seen = false;
    if (!opts.bump || !v->next) continue;
    if (queue.assigned == idx)
      queue.assigned = v->prev ? v->prev : v->next;
    dequeue (v), enqueue (v, idx);
    v->bumped = ++stats.bumped;
    if (idx != uip && !vals[idx]) queue.assigned = idx;
    LOG ("bumped and moved to front %d", idx);
    check_vmtf_queue_invariant ();
  }
  seen.literals.clear ();
  STOP (bump);
}

struct resolved_earlier {
  bool operator () (Clause * a, Clause * b) {
    return a->resolved () < b->resolved ();
  }
};

static void bump_resolved_clauses () {
  START (bump);
  sort (resolved.begin (), resolved.end (), resolved_earlier ());
  for (size_t i = 0; i < resolved.size (); i++)
    resolved[i]->resolved () = ++stats.resolved;
  STOP (bump);
  resolved.clear ();
}

static void clear_levels () {
  for (size_t i = 0; i < seen.levels.size (); i++)
    levels[seen.levels[i]].reset ();
  seen.levels.clear ();
}

static void resolve_clause (Clause * c) {
  if (!c->redundant) return;
  UPDATE (avg.resolved.size, c->size);
  UPDATE (avg.resolved.glue, c->glue);
  if (c->size <= opts.keepsize) return;
  if (c->glue <= (unsigned) opts.keepglue) return;
  resolved.push_back (c);
}

static bool analyze_literal (int lit) {
  Var & v = var (lit);
  if (v.seen) return false;
  if (!v.level) return false;
  assert (val (lit) < 0);
  if (v.level < level) clause.push_back (lit);
  Level & l = levels[v.level];
  if (!l.seen++) {
    LOG ("found new level %d contributing to conflict");
    seen.levels.push_back (v.level);
  }
  if (v.trail < l.trail) l.trail = v.trail;
  v.seen = true;
  seen.literals.push_back (lit);
  LOG ("analyzed literal %d assigned at level %d", lit, v.level);
  return v.level == level;
}

static bool blocking_enabled () {
  if (stats.conflicts > blocking.limit) {
    if (blocking.exploring) {
      blocking.inc += opts.restartblocklimit;
      blocking.limit = stats.conflicts + blocking.inc;
      blocking.exploring = false;
      msg ("average blocking glue %.2f non-blocking %.2f ratio %.2f",
        (double) avg.glue.blocking, (double) avg.glue.nonblocking,
        relative (avg.glue.blocking, avg.glue.nonblocking));
      if (avg.glue.blocking >
          opts.restartblockmargin * avg.glue.nonblocking) {
        msg ("exploiting non-blocking until %ld conflicts", blocking.limit);
        blocking.enabled = false;
      } else {
        msg ("exploiting blocking until %ld conflicts", blocking.limit);
        blocking.enabled = true;
      }
    } else {
      blocking.exploring = true;
      blocking.limit =
        stats.conflicts + max (blocking.inc/10, (long)opts.restartblocklimit);
      if (blocking.enabled) {
        msg ("exploring non-blocking until %ld conflicts", blocking.limit);
        blocking.enabled = false;
      } else {
        msg ("exploring blocking until %ld conflicts", blocking.limit);
        blocking.enabled = true;
      }
    }
  }
  return blocking.enabled;
}

struct trail_greater_than {
  bool operator () (int a, int b) { return var (a).trail > var (b).trail; }
};

static void analyze () {
  assert (conflict);
  assert (clause.empty ());
  assert (seen.literals.empty ());
  assert (seen.levels.empty ());
  assert (resolved.empty ());
  START (analyze);
  if (!level) learn_empty_clause ();
  else {
    Reason & reason = conflict;
    LOG (reason.clause (), "analyzing conflict");
    if (reason.referenced ()) resolve_clause (reason.clause ());
    int open = 0, uip = 0;
    size_t i = trail.size ();
    for (;;) {
      const int size = reason->size, * lits = reason->literals;;
      for (int j = 0; j < size; j++)
        if (analyze_literal (lits[j])) open++;
      while (!var (uip = trail[--i]).seen)
        ;
      if (!--open) break;
      reason = var (uip).reason;
      LOG (reason.clause (), "analyzing %d reason", uip);
    }
    LOG ("first UIP %d", uip);
    clause.push_back (-uip);
    check_clause ();
    bump_resolved_clauses ();
    const int size = (int) clause.size ();
    const int glue = (int) seen.levels.size ();
    LOG ("1st UIP clause of size %d and glue %d", size, glue);
    UPDATE (avg.glue.slow, glue);
    UPDATE (avg.glue.fast, glue);
    if (blocking.enabled) UPDATE (avg.glue.blocking, glue);
    else                  UPDATE (avg.glue.nonblocking, glue);
    if (opts.minimize) minimize_clause ();
    Clause * driving_clause = 0;
    int jump = 0;
    if (size > 1) {
      sort (clause.begin (), clause.end (), trail_greater_than ());
      driving_clause = new_learned_clause (glue);
      jump = var (clause[1]).level;
    }
    stats.learned.unit += (size == 1);
    stats.learned.binary += (size == 2);
    UPDATE (avg.frequency.unit, (size == 1) ? inc.unit : 0);
    UPDATE (avg.jump, jump);
    UPDATE (avg.trail, trail.size ());
    if (opts.restartblocking &&
        stats.conflicts >= limits.restart.conflicts &&
        blocking_enabled () &&
        trail.size () > opts.restartblock * avg.trail) {
      LOG ("blocked restart");
      limits.restart.conflicts = stats.conflicts + opts.restartint;
      stats.restart.blocked++;
    }
    backtrack (jump);
    assign (-uip, driving_clause);
    bump_and_clear_seen_variables (uip);
    clause.clear (), clear_levels ();
  }
  conflict = NoReason ();
  STOP (analyze);
}

static bool satisfied () { return trail.size () == (size_t) max_var; }

/*------------------------------------------------------------------------*/

static bool restarting () {
  if (!opts.restart) return false;
  if (stats.conflicts <= limits.restart.conflicts) return false;
  stats.restart.tried++;
  limits.restart.conflicts = stats.conflicts + opts.restartint;
  double s = avg.glue.slow, f = avg.glue.fast, l = opts.restartmargin * s;
  LOG ("EMA learned glue slow %.2f fast %.2f limit %.2f", s, f, l);
  if (l > f) {
    if (opts.restartemaf1) {
      if (avg.frequency.unit >= opts.emaf1lim) {
        stats.restart.unit++;
        LOG ("high unit frequency restart", (double) avg.frequency.unit);
        return true;
      } else LOG ("low unit frequency", (double) avg.frequency.unit);
    }
    stats.restart.unforced++;
    LOG ("unforced restart");
    return false;
  } else {
    LOG ("forced restart");
    stats.restart.forced++;
  }
  if (opts.restartdelaying) {
    double j = avg.jump; l = opts.restartdelay * j;
    LOG ("EMA jump %.2f limit %.2f", j, l);
    if (level < l) {
      stats.restart.delayed++;
      LOG ("delayed restart");
      return false;
    } else LOG ("undelayed restart");
  }
  return true;
}

static int reusetrail () {
  if (!opts.reusetrail) return 0;
  long limit = var (next_decision_variable ()).bumped;
  int res = 0;
  while (res < level && var (levels[res + 1].decision).bumped > limit)
    res++;
  if (res) { stats.restart.reused++; LOG ("reusing trail %d", res); }
  return res;
}

static void restart () {
  START (restart);
  stats.restart.count++;
  LOG ("restart %ld", stats.restart.count);
  backtrack (reusetrail ());
  report ('r', 1);
  STOP (restart);
}

/*------------------------------------------------------------------------*/

static bool reducing () {
  if (!opts.reduce) return false;
  return stats.conflicts >= limits.reduce.conflicts;
}

static void protect_reasons () {
  for (size_t i = 0; i < trail.size (); i++) {
    Var & v = var (trail[i]);
    if (v.level && v.reason.referenced ())
      v.reason.clause ()->reason = true;
  }
}

static void unprotect_reasons () {
  for (size_t i = 0; i < trail.size (); i++) {
    Var & v = var (trail[i]);
    if (v.level && v.reason.referenced ())
      assert (v.reason.clause ()->reason),
      v.reason.clause ()->reason = false;
  }
}

// This function returns 1 if the given clause is root level satisfied or -1
// if it is not root level satisfied but contains a root level falsified
// literal and 0 otherwise, if it does not contain a root level fixed
// literal.

static int clause_contains_fixed_literal (Clause * c) {
  const int * lits = c->literals, size = c->size;
  int res = 0;
  for (int i = 0; res <= 0 && i < size; i++) {
    const int lit = lits[i];
    const int tmp = fixed (lit);
   if (tmp > 0) {
     LOG (c, "root level satisfied literal %d in", lit);
     res = 1;
   } else if (!res && tmp < 0) {
     LOG (c, "root level falsified literal %d in", lit);
     res = -1;
    }
  }
  return res;
}

// Assume that the clause is not root level satisfied but contains a literal
// set to false (root level falsified literal), so it can be shrunken.  The
// clause data is not actually reallocated at this point to avoid dealing
// with issues of special policies for watching binary clauses or whether a
// clause is extended or not. Only its size field is adjusted accordingly
// after flushing out root level falsified literals.

static void flush_falsified_literals (Clause * c) {
  if (c->reason || c->size == 2) return;
  trace_flushing_clause (c);
  const int size = c->size;
  int * lits = c->literals, j = 0;
  for (int i = 0; i < size; i++) {
    const int lit = lits[j++] = lits[i];
    const int tmp = fixed (lit);
    assert (tmp <= 0);
    if (tmp >= 0) continue;
    LOG ("flushing %d", lit);
    j--;
  }
  int flushed = c->size - j;
  stats.reduce.bytes += flushed * sizeof (int);
  for (int i = j; i < size; i++) lits[i] = 0;
  c->size = j;
  LOG (c, "flushed %d literals and got", flushed);
}

static void mark_satisfied_clauses_as_garbage () {
  for (size_t i = 0; i < clauses.size (); i++) {
    Clause * c = ref2clause (clauses[i]);
    if (c->garbage) continue;
    const int tmp = clause_contains_fixed_literal (c);
         if (tmp > 0) c->garbage = true;
    else if (tmp < 0) flush_falsified_literals (c);
  }
}

struct glue_larger {
  bool operator () (Clause * c, Clause * d) {
    if (c->glue > d->glue) return true;
    if (c->glue < d->glue) return false;
    return resolved_earlier () (c, d);
  }
};

// This function implements the important reduction policy. It determines
// which redundant clauses are considered not useful and thus will be
// collected in a subsequent garbage collection phase.

static void mark_useless_redundant_clauses_as_garbage () {
  vector<Clause*> stack;
  assert (stack.empty ());
  const long delta_resolved = stats.resolved - limits.reduce.resolved;
  const long limit_resolved =
    limits.reduce.resolved + (1.0 - opts.reduceresolved) * delta_resolved;
  for (size_t i = 0; i < clauses.size (); i++) {
    Clause * c = ref2clause (clauses[i]);
    if (!c->redundant) continue;                // keep irredundant
    if (c->reason) continue;                    // need to keep reasons
    if (c->garbage) continue;                   // already marked

    // If the clause is short or has small glue keep it.
    //
    if (c->size <= opts.keepsize) continue;
    if (c->glue <= (unsigned) opts.keepglue) continue;

    // If the clause has recently been resolved or generated keep it.
    //
    if (opts.reducefocus &&
        c->size <= opts.reducefocusize &&
        c->glue <= opts.reducefocusglue &&
        c->resolved () > limit_resolved) continue;

    // In dynamic reduction we estimate the average glue and size of
    // resolved clauses in conflict analysis and always keep clauses which
    // are below both limits.
    //
    if (opts.reducedynamic &&
        c->glue < avg.resolved.glue &&
        c->size < avg.resolved.size) continue;

    stack.push_back (c);        // clause is garbage collection candidate
  }
  if (opts.reduceglue) sort (stack.begin (), stack.end (), glue_larger ());
  else sort (stack.begin (), stack.end (), resolved_earlier ());
  const size_t target = stack.size ()/2;
  for (size_t i = 0; i < target; i++) {
    LOG (stack[i], "marking useless to be collected");
    stack[i]->garbage = true;
  }
}

static void setup_binaries () {
  if (others) {
    dec_bytes (size_others * sizeof (int));
    delete [] others;
    others = 0;
  }
  int * num_binaries = new int[max_lit + 1];
  inc_bytes ((max_lit + 1) * sizeof (int));
  for (int l = min_lit; l <= max_lit; l++) num_binaries[l] = 0;
  for (size_t i = 0; i < clauses.size (); i++) {
    Clause * c = ref2clause (clauses[i]);
    if (c->garbage || c->size != 2) continue;
    int l0 = c->literals[0], l1 = c->literals[1];
    num_binaries[vlit (l0)]++, num_binaries[vlit (l1)]++;
  }
  size_others = 0;
  for (int l = min_lit, count; l <= max_lit; l++)
    if ((count = num_binaries[l]))
      size_others += count + 1;
  LOG ("initializing others table of size %ld", size_others);
  inc_bytes (size_others * sizeof (int));
  others = new int[size_others];
  int * p = others + size_others;
  for (int sign = -1; sign <= 1; sign += 2) {
    for (int idx = queue.last; idx; idx = var (idx).prev) {
      const int lit = sign * phases[idx] * idx;
      const int count = num_binaries [ vlit (lit) ];
      if (count) {
        *(binaries (lit) = --p) = 0;
        p -= count;
      } else binaries (lit) = 0;
    }
  }
  assert (p == others);
  dec_bytes ((max_lit + 1) * sizeof (int));
  delete [] num_binaries;
  for (size_t i = 0; i < clauses.size (); i++) {
    Clause * c = ref2clause (clauses[i]);
    if (c->garbage || c->size != 2) continue;
    int l0 = c->literals[0], l1 = c->literals[1];
    *--binaries (l0) = l1, *--binaries (l1) = l0;
  }
}

static void setup_watches () {
  size_t bytes = 0;
  for (int idx = 1; idx <= max_var; idx++) {
    for (int sign = -1; sign <= 1; sign += 2) {
      const int lit = sign * idx;
      Watches & ws = watches (lit);
      bytes += ws.capacity () * sizeof ws[0];
      if (fixed (lit)) ws = Watches ();
      else ws.clear ();
    }
  }
  stats.bytes.watcher.current = bytes;
  if (bytes > stats.bytes.watcher.max) stats.bytes.watcher.max = bytes;
  for (size_t i = 0; i < clauses.size (); i++) {
    Clause * c = ref2clause (clauses[i]);
    if (c->size > 2) watch_clause (c);
  }
}

// TODO ugly ... should be replaced by copying version?

static void compactifying_garbage_collector () {
  size_t collected_bytes = 0, i = 0, j = i;
  const size_t size = clauses.size ();
  char * new_top = 0;
  while (i < size) {
    assert (!i || clauses[i-1] < clauses[i]);
    Ref old_ref = clauses[i++];
    Clause * c = (Clause*) arena.ref2ptr (old_ref);
    char * ptr = (char *) c;
    size_t bytes = c->bytes ();
    int forced;
    if (c->reason) {
      forced = c->literals[0];
      if (val (forced) < 0) forced = c->literals[1];
      else assert (val (c->literals[1]) < 0);
      assert (val (forced) > 0);
    } else forced = 0;
    const bool extended = c->extended;
    if (extended) ptr -= EXTENDED_OFFSET;
    if (!new_top) new_top = ptr;
    if (c->reason || !c->garbage) {
      if (ptr != new_top) {
        memmove (new_top, ptr, bytes);
        Ref new_ref = arena.ptr2ref (new_top);
        if (extended) new_ref += EXTENDED_OFFSET/alignment;
        clauses[j++] = new_ref;
        if (forced) {
          Var & v = var (forced);
          assert (v.reason.reference () == old_ref);
          v.reason.update_reference (new_ref);
        }
      } else j++;
      new_top += align (bytes);
    } else {
      LOG (c, "delete");
      if (c->redundant)
           assert (stats.clauses.redundant),   stats.clauses.redundant--;
      else assert (stats.clauses.irredundant), stats.clauses.irredundant--;
      assert (stats.clauses.current);
      stats.clauses.current--;
      stats.reduce.clauses++;
      stats.reduce.bytes += bytes;
      collected_bytes += bytes;
      trace_delete_clause (c);
    }
  }
  clauses.resize (j);
  if (new_top) arena.resize (new_top);
  LOG ("collected %ld bytes", collected_bytes);
}

// TODO Still pretty ugly ... simplify? needed?

static void copying_garbage_collector () {
  Arena new_arena;
  new_arena.enlarge (arena.size () - alignment);
  for (size_t k = 0; k < clauses.size (); k++) {
    Ref old_ref = clauses[k];
    Clause * c = ref2clause (old_ref);
    if (c->size != 2 || c->garbage) continue;
    char * old_ptr = (char *) c;
    size_t bytes = c->bytes ();
    Ref new_ref;
    char * new_ptr = (char*) new_arena.allocate (bytes, new_ref);
    memcpy (new_ptr, old_ptr, bytes);
    LOG ((Clause*) new_arena.ref2ptr (new_ref),
      "old reference %u now %u",
      (unsigned) old_ref, (unsigned) new_ref);
    c->literals[0] = 0;
    c->literals[1] = new_ref;
  }
  for (int sign = -1; sign <= 1; sign += 2) {
    for (int idx = queue.last; idx; idx = var (idx).prev) {
      if (fixed (idx)) continue;
      const int lit = sign * phases[idx] * idx;
      LOG ("moving non-garbage clauses with %d", lit);
      Watches & ws = watches (lit);
      for (size_t k = 0; k < ws.size (); k++) {
        Ref old_ref = ws[k].ref;
        Clause * c = (Clause*) arena.ref2ptr (old_ref);
        if (!c->reason && c->garbage) continue;
        if (!c->literals[0]) {
          LOG ("reference %u already moved to %u",
            (unsigned) old_ref, (unsigned) c->literals[1]);
          continue;
        }
        char * old_ptr = (char *) c;
        size_t bytes = c->bytes ();
        const bool extended = c->extended;
        if (extended) old_ptr -= EXTENDED_OFFSET;
        Ref new_ref;
        void * new_ptr = new_arena.allocate (bytes, new_ref);
        memcpy (new_ptr, old_ptr, bytes);
        if (extended) new_ref += EXTENDED_OFFSET/alignment;
        LOG ((Clause*) new_arena.ref2ptr (new_ref),
          "old reference %u now %u literal %d",
          (unsigned) old_ref, (unsigned) new_ref, lit);
        c->literals[0] = 0;
        c->literals[1] = new_ref;
      }
    }
  }
  if (level > 0) {
    for (size_t k = var (levels[1].decision).trail; k < trail.size (); k++) {
      const int lit = trail[k];
      Var & v = var (lit);
      if (!v.reason.referenced ()) continue;
      Clause * c = ref2clause (v.reason.reference ());
      assert (c->reason), assert (!c->literals[0]);
      v.reason.update_reference (c->literals[1]);
    }
  }
  size_t collected_bytes = 0, moved_bytes = 0, i = 0, j = i;
  while (i < clauses.size ()) {
    Ref old_ref = clauses[i++];
    Clause * c = (Clause*) arena.ref2ptr (old_ref);
    size_t bytes = c->bytes ();
    if (c->reason || !c->garbage) {
      assert (!c->literals[0]);
      assert ((unsigned) c->literals[1] < new_arena.size () / alignment );
      clauses[j++] = c->literals[1];
      moved_bytes += bytes;
    } else {
      LOG (c, "delete");
      if (c->redundant)
           assert (stats.clauses.redundant),   stats.clauses.redundant--;
      else assert (stats.clauses.irredundant), stats.clauses.irredundant--;
      assert (stats.clauses.current);
      stats.clauses.current--;
      stats.reduce.clauses++;
      stats.reduce.bytes += bytes;
      collected_bytes += bytes;
      trace_delete_clause (c);
    }
  }
  clauses.resize (j);
  LOG ("collected %ld bytes", collected_bytes);
  arena.release_and_take_over_memory (new_arena);
}

static void garbage_collection () {
  if (opts.copying) copying_garbage_collector ();
  else compactifying_garbage_collector ();
}

static void reduce () {
  START (reduce);
  stats.reduce.count++;
  LOG ("reduce %ld resolved limit %ld",
    stats.reduce.count, limits.reduce.resolved);
  protect_reasons ();
  const bool new_units = (limits.reduce.fixed < stats.fixed);
  if (new_units) mark_satisfied_clauses_as_garbage ();
  mark_useless_redundant_clauses_as_garbage ();
  garbage_collection ();
  unprotect_reasons ();
  setup_binaries ();
  setup_watches ();
  inc.reduce.conflicts += opts.reduceinc;
  limits.reduce.conflicts = stats.conflicts + inc.reduce.conflicts;
  limits.reduce.resolved = stats.resolved;
  limits.reduce.fixed = stats.fixed;
  report ('-');
  STOP (reduce);
}

/*------------------------------------------------------------------------*/

static void decide () {
  START (decide);
  level++;
  stats.decisions++;
  int idx = next_decision_variable ();
  int decision = phases[idx] * idx;
  levels.push_back (Level (decision));
  LOG ("decide %d", decision);
  assign (decision, DecisionReason ());
  STOP (decide);
}

static void iterate () { iterating = false; report ('i'); }

static int search () {
  int res = 0;
  START (search);
  while (!res)
         if (unsat) res = 20;
    else if (!propagate ()) analyze ();
    else if (iterating) iterate ();
    else if (satisfied ()) res = 10;
    else if (restarting ()) restart ();
    else if (reducing ()) reduce ();
    else decide ();
  STOP (search);
  return res;
}

/*------------------------------------------------------------------------*/

#define INIT_EMA(E,V) \
  E = EMA (V); \
  LOG ("init " #E " EMA target alpha %g", (double) V)

static void init_solving () {
  limits.restart.conflicts = opts.restartint;
  limits.reduce.conflicts = opts.reduceinit;
  inc.reduce.conflicts = opts.reduceinit;
  inc.unit = opts.emaf1 ? 1.0 / opts.emaf1 : 1e-9;
  INIT_EMA (avg.glue.fast, opts.emagluefast);
  INIT_EMA (avg.frequency.unit, opts.emaf1);
  INIT_EMA (avg.resolved.glue, opts.emaresolved);
  INIT_EMA (avg.resolved.size, opts.emaresolved);
  INIT_EMA (avg.jump, opts.emajump);
  INIT_EMA (avg.trail, opts.ematrail);
  blocking.limit = blocking.inc = opts.restartblocklimit;
}

static int solve () {
  init_solving ();
  section ("solving");
  if (clashing_unit) { learn_empty_clause (); return 20; }
  else return search ();
}

/*------------------------------------------------------------------------*/

static void print_statistics () {
  double t = seconds ();
  size_t m = max_bytes ();
  print_profile (t);
  section ("statistics");
  msg ("conflicts:     %15ld   %10.2f    per second",
    stats.conflicts, relative (stats.conflicts, t));
  msg ("decisions:     %15ld   %10.2f    per second",
    stats.decisions, relative (stats.decisions, t));
  msg ("propagations:  %15ld   %10.2f    millions per second",
    stats.propagations, relative (stats.propagations/1e6, t));
  msg ("reductions:    %15ld   %10.2f    conflicts per reduction",
    stats.reduce.count, relative (stats.conflicts, stats.reduce.count));
  msg ("restarts:      %15ld   %10.2f    conflicts per restart",
    stats.restart.count, relative (stats.conflicts, stats.restart.count));
  msg ("reused:        %15ld   %10.2f %%  per restart",
    stats.restart.reused,
    percent (stats.restart.reused, stats.restart.count));
  msg ("blocked:       %15ld   %10.2f %%  per restart",
    stats.restart.blocked,
    percent (stats.restart.blocked, stats.restart.count));
  msg ("delayed:       %15ld   %10.2f %%  per restart",
    stats.restart.delayed,
    percent (stats.restart.delayed, stats.restart.count));
  msg ("unforced:      %15ld   %10.2f %%  per restart",
    stats.restart.unforced,
    percent (stats.restart.unforced, stats.restart.count));
  msg ("forced:        %15ld   %10.2f %%  per restart",
    stats.restart.forced,
    percent (stats.restart.forced, stats.restart.count));
  msg ("f1restart:     %15ld   %10.2f %%  per restart",
    stats.restart.unit,
    percent (stats.restart.unit, stats.restart.count));
  msg ("units:         %15ld   %10.2f    conflicts per unit",
    stats.learned.unit, relative (stats.conflicts, stats.learned.unit));
  msg ("binaries:      %15ld   %10.2f    conflicts per binary",
    stats.learned.binary, relative (stats.conflicts, stats.learned.binary));
  msg ("trailsorted:   %15ld   %10.2f %%  per conflict",
    stats.trailsorted, percent (stats.trailsorted, stats.conflicts));
  msg ("bumped:        %15ld   %10.2f    per conflict",
    stats.bumped, relative (stats.bumped, stats.conflicts));
  msg ("resolved:      %15ld   %10.2f    per conflict",
    stats.resolved, relative (stats.resolved, stats.conflicts));
  msg ("searched:      %15ld   %10.2f    per decision",
    stats.searched, relative (stats.searched, stats.decisions));
  long learned = stats.literals.learned - stats.literals.minimized;
  msg ("learned:       %15ld   %10.2f    per conflict",
    learned, relative (learned, stats.conflicts));
  msg ("minimized:     %15ld   %10.2f %%  of 1st-UIP-literals",
    stats.literals.minimized,
    percent (stats.literals.minimized, stats.literals.learned));
  msg ("collected:     %15ld   %10.2f    clauses and MB",
    stats.reduce.clauses, stats.reduce.bytes/(double)(1l<<20));
  msg ("maxbytes:      %15ld   %10.2f    MB",
    m, m/(double)(1l<<20));
  msg ("time:          %15s   %10.2f    seconds", "", t);
  msg ("");
}

static void init_vmtf_queue () {
  int prev = 0, start, end, dir;
  if (opts.reverse) start = 1, end = max_var + 1, dir = 1;
  else start = max_var, end = 0, dir = -1;
  for (int i = start; i != end; i += dir) {
    Var * v = &vars[i];
    if ((v->prev = prev)) var (prev).next = i;
    else queue.first = i;
    v->bumped = ++stats.bumped;
    prev = i;
  }
  queue.last = queue.assigned = prev;
}

static void reset_signal_handlers (void) {
#define SIGNAL(SIG) \
  (void) signal (SIG, SIG ## _handler);
SIGNALS
#undef SIGNAL
}

static const char * signal_name (int sig) {
#define SIGNAL(SIG) \
  if (sig == SIG) return # SIG; else
  SIGNALS
#undef SIGNAL
  return "UNKNOWN";
}

static void catchsig (int sig) {
  if (!catchedsig) {
    catchedsig = true;
    msg ("");
    msg ("CAUGHT SIGNAL %d %s", sig, signal_name (sig));
    section ("result");
    msg ("s UNKNOWN");
    print_statistics ();
  }
  reset_signal_handlers ();
  msg ("RERAISING SIGNAL %d %s", sig, signal_name (sig));
  raise (sig);
}

static void init_signal_handlers (void) {
#define SIGNAL(SIG) \
  SIG ## _handler = signal (SIG, catchsig);
SIGNALS
#undef SIGNAL
}

#define NEW(P,T,N) \
  P = new T[N], inc_bytes ((N) * sizeof (T))

static void init_variables () {
  min_lit = 2, max_lit = 2*max_var + 1;
  NEW (vals,        signed char, max_var + 1);
  NEW (phases,      signed char, max_var + 1);
  NEW (vars,                Var, max_var + 1);
  NEW (literal.watches, Watches, max_lit + 1);
  NEW (literal.binaries,  int *, max_lit + 1);
  for (int i = 1; i <= max_var; i++) vals[i] = 0;
  for (int i = 1; i <= max_var; i++) phases[i] = -1;
  for (int l = min_lit; l <= max_lit; l++) literal.binaries [l] = 0;
  init_vmtf_queue ();
  msg ("initialized %d variables", max_var);
  levels.push_back (Level (0));
}

#define printf_bool_FMT   "%s"
#define printf_int_FMT    "%d"
#define printf_double_FMT "%g"

#define printf_bool_CONV(V)    ((V) ? "true" : "false")
#define printf_int_CONV(V)     ((int)(V))
#define printf_double_CONV(V)  ((double)(V))

static void print_options () {
  section ("options");
#define OPTION(N,T,V,L,H,D) \
  msg ("--" #N "=" printf_ ## T ## _FMT, printf_ ## T ## _CONV (opts.N));
  OPTIONS
#undef OPTION
}

static void reset () {
#ifndef NDEBUG
  if (others) delete [] others;
  arena.release ();
  delete [] literal.binaries;
  delete [] literal.watches;
  delete [] vars;
  delete [] vals;
  delete [] phases;
  if (solution) delete [] solution;
#endif
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

static void print_usage () {
  fputs (
"usage: cadical [ <option> ... ] [ <input> [ <proof> ] ]\n"
"\n"
"where '<option>' is one of the following short options\n"
"\n"
"  -h         print this command line option summary\n"
"  -n         do not print witness\n"
"  -q         quiet (same as '--quiet')\n"
"  -v         more verbose messages (same as '--verbose')\n"
#ifndef NDEBUG
"  -s <sol>   read solution in competition output format\n"
"             (used for testing and debugging only)\n"
#endif
"\n"
"or '<option>' can be one of the following long options\n"
"\n",
  stdout);
#define OPTION(N,T,V,L,H,D) \
  printf ( \
    "  %-26s " D " [" printf_ ## T ## _FMT "]\n", \
    "--" #N "=<" #T ">", printf_ ## T ## _CONV ((T)(V)));
  OPTIONS
#undef OPTION
  fputs (
"\n"
"The long options have their default value printed in brackets\n"
"after their description.  They can also be used in the form\n"
"'--<name>' which is equivalent to '--<name>=1' and in the form\n"
"'--no-<name>' which is equivalent to '--<name>=0'.\n"
"\n"
"Note that decimal integers are casted to 'double' and 'bool'\n"
"in the natural way, e.g., '1' is interpreted as 'true'.\n"
"\n"
"Then '<input>' is a (compressed) DIMACS file and '<output>'\n"
"is a file to store the DRAT proof.  If no '<proof>' file is\n"
"specified, then no proof is generated.  If no '<input>' is given\n"
"then '<stdin>' is used. If '-' is used as '<input>' then the\n"
"solver reads from '<stdin>'.  If '-' is specified for '<proof>'\n"
"then the proof is generated and printed to '<stdout>'.\n",
  stdout);
}

/*------------------------------------------------------------------------*/

static bool set_option (bool & opt, const char * name,
                        const char * valstr, const bool l, const bool h) {
  assert (!l), assert (h);
       if (!strcmp (valstr, "true")  || !strcmp (valstr, "1")) opt = true;
  else if (!strcmp (valstr, "false") || !strcmp (valstr, "0")) opt = false;
  else return false;
  LOG ("set option --%s=%d", name, opt);
  return true;
}

static bool set_option (int & opt, const char * name,
                        const char * valstr, const int l, const int h) {
  assert (l < h);
  int val = atoi (valstr);              // TODO check valstr to be valid
  if (val < l) val = l;
  if (val > h) val = h;
  opt = val;
  LOG ("set option --%s=%d", name, opt);
  return true;
}

static bool set_option (double & opt, const char * name,
                        const char * valstr,
                        const double l, const double h) {
  assert (l < h);
  double val = atof (valstr);           // TODO check valstr to be valid
  if (val < l) val = l;
  if (val > h) val = h;
  opt = val;
  LOG ("set option --%s=%g", name, opt);
  return true;
}

static const char *
match_option (const char * arg, const char * name) {
  if (arg[0] != '-' || arg[1] != '-') return 0;
  const bool no = (arg[2] == 'n' && arg[3] == 'o' && arg[4] == '-');
  const char * p = arg + (no ? 5 : 2), * q = name;
  while (*q) if (*q++ != *p++) return 0;
  if (!*p) return no ? "0" : "1";
  if (*p++ != '=') return 0;
  return p;
}

static bool set_option (const char * arg) {
  const char * valstr;
#define OPTION(N,T,V,L,H,D) \
  if ((valstr = match_option (arg, # N))) \
    return set_option (opts.N, # N, valstr, L, H); \
  else
  OPTIONS
#undef OPTION
  return false;
}

/*------------------------------------------------------------------------*/

static int nextch () {
  int res = getc_unlocked (input_file);
  if (res == '\n') lineno++;
  return res;
}

static void parse_string (const char * str, char prev) {
  for (const char * p = str; *p; p++)
    if (nextch () == *p) prev = *p;
    else perr ("expected '%c' after '%c'", *p, prev);
}

static int parse_positive_int (int ch, int & res, const char * name) {
  assert (isdigit (ch));
  res = ch - '0';
  while (isdigit (ch = nextch ())) {
    int digit = ch - '0';
    if (INT_MAX/10 < res || INT_MAX - digit < 10*res)
      perr ("too large '%s' in header", name);
    res = 10*res + digit;
  }
  return ch;
}

static int parse_lit (int ch, int & lit) {
  int sign = 0;
  if (ch == '-') {
    if (!isdigit (ch = nextch ())) perr ("expected digit after '-'");
    sign = -1;
  } else if (!isdigit (ch)) perr ("expected digit or '-'");
  else sign = 1;
  lit = ch - '0';
  while (isdigit (ch = nextch ())) {
    int digit = ch - '0';
    if (INT_MAX/10 < lit || INT_MAX - digit < 10*lit)
      perr ("literal too large");
    lit = 10*lit + digit;
  }
  if (ch == '\r') ch = nextch ();
  if (ch != 'c' && ch != ' ' && ch != '\t' && ch != '\n')
    perr ("expected white space after '%d'", sign*lit);
  if (lit > max_var)
    perr ("literal %d exceeds maximum variable %d", sign*lit, max_var);
  lit *= sign;
  return ch;
}

static void parse_dimacs () {
  int ch;
  assert (dimacs_name), assert (dimacs_file);
  START (parse);
  input_name = dimacs_name;
  input_file = dimacs_file;
  lineno = 1;
  for (;;) {
    ch = nextch ();
    if (ch != 'c') break;
    while ((ch = nextch ()) != '\n')
      if (ch == EOF)
        perr ("unexpected end-of-file in header comment");
  }
  if (ch != 'p') perr ("expected 'c' or 'p'");
  parse_string (" cnf ", 'p');
  if (!isdigit (ch = nextch ())) perr ("expected digit after 'p cnf '");
  ch = parse_positive_int (ch, max_var, "<max-var>");
  if (ch != ' ') perr ("expected ' ' after 'p cnf %d'", max_var);
  if (!isdigit (ch = nextch ()))
    perr ("expected digit after 'p cnf %d '", max_var);
  ch = parse_positive_int (ch, num_original_clauses, "<num-clauses>");
  while (ch == ' ' || ch == '\r') ch = nextch ();
  if (ch != '\n') perr ("expected new-line after 'p cnf %d %d'",
                        max_var, num_original_clauses);
  msg ("found 'p cnf %d %d' header", max_var, num_original_clauses);
  init_variables ();
  int lit = 0, parsed_clauses = 0;
  while ((ch = nextch ()) != EOF) {
    if (ch == ' ' || ch == '\n' || ch == '\t' || ch == '\r') continue;
    if (ch == 'c') {
COMMENT:
      while ((ch = nextch ()) != '\n')
        if (ch == EOF) perr ("unexpected end-of-file in body comment");
      continue;
    }
    if (parse_lit (ch, lit) == 'c') goto COMMENT;
#ifndef NDEBUG
    original_literals.push_back (lit);
#endif
    if (lit) {
      if (clause.size () == INT_MAX) perr ("clause too large");
      clause.push_back (lit);
    } else {
      if (!tautological ()) add_new_original_clause ();
      else LOG ("tautological original clause");
      clause.clear ();
      if (parsed_clauses++ >= num_original_clauses) perr ("too many clauses");
    }
  }
  if (lit) perr ("last clause without '0'");
  if (parsed_clauses < num_original_clauses) perr ("clause missing");
  msg ("parsed %d clauses in %.2f seconds", parsed_clauses, seconds ());
  STOP (parse);
}

#ifndef NDEBUG

static void parse_solution () {
  assert (solution_name), assert (solution_file);
  START (parse);
  input_name = solution_name;
  input_file = solution_file;
  lineno = 1;
  NEW (solution, signed char, max_var + 1);
  for (int i = 1; i <= max_var; i++) solution[i] = 0;
  int ch;
  for (;;) {
    ch = nextch ();
    if (ch == EOF) perr ("missing 's' line");
    if (ch == 'c') {
      while ((ch = nextch ()) != '\n')
        if (ch == EOF) perr ("unexpected end-of-file in comment");
    }
    if (ch == 's') break;
    perr ("expected 'c' or 's'");
  }
  parse_string (" SATISFIABLE", 's');
  if ((ch = nextch ()) == '\r') ch = nextch ();
  if (ch != '\n') perr ("expected new-line after 's SATISFIABLE'");
  int count = 0;
  for (;;) {
    ch = nextch ();
    if (ch != 'v') perr ("expected 'v' at start-of-line");
    if ((ch = nextch ()) != ' ') perr ("expected ' ' after 'v'");
    int lit = 0;
    ch = nextch ();
    do {
      if (ch == ' ' || ch == '\t') { ch = nextch (); continue; }
      if ((ch = parse_lit (ch, lit)) == 'c') perr ("unexpected comment");
      if (!lit) break;
      if (solution[abs (lit)]) perr ("variable %d occurs twice", abs (lit));
      LOG ("solution %d", lit);
      solution [abs (lit)] = sign (lit);
      count++;
      if (ch == '\r') ch = nextch ();
    } while (ch != '\n');
    if (!lit) break;
  }
  msg ("parsed %d solutions %.2f%%", count, percent (count, max_var));
  STOP (parse);
}

#endif

static void check_satisfying_assignment (int (*assignment)(int)) {
#ifndef NDEBUG
  bool satisfied = false;
  size_t start = 0;
  for (size_t i = 0; i < original_literals.size (); i++) {
    int lit = original_literals[i];
    if (!lit) {
      if (!satisfied) {
        fflush (stdout);
        fputs ("*** cadical error: unsatisfied clause:\n", stderr);
        for (size_t j = start; j < i; j++)
          fprintf (stderr, "%d ", original_literals[j]);
        fputs ("0\n", stderr);
        fflush (stderr);
        abort ();
      }
      satisfied = false;
      start = i + 1;
    } else if (!satisfied && assignment (lit) > 0) satisfied = true;
  }
  msg ("satisfying assignment checked");
#endif
}

static void print_witness () {
  int c = 0;
  for (int i = 1; i <= max_var; i++) {
    if (!c) print ('v', stdout), c = 1;
    char str[20];
    sprintf (str, " %d", val (i) < 0 ? -i : i);
    int l = strlen (str);
    if (c + l > 78) print ("\nv", stdout), c = 1;
    print (str, stdout);
    c += l;
  }
  if (c) print ('\n', stdout);
  print ("v 0\n", stdout);
  fflush (stdout);
}

static void banner () {
  section ("banner");
  msg ("CaDiCaL Radically Simplified CDCL SAT Solver");
  msg ("Version " VERSION " " GITID);
  msg ("Copyright (c) 2016 Armin Biere, JKU");
  msg (COMPILE);
}

int main (int argc, char ** argv) {
  int i, res;
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h")) print_usage (), exit (0);
    else if (!strcmp (argv[i], "--version"))
      fputs (VERSION "\n", stdout), exit (0);
    else if (!strcmp (argv[i], "-")) {
      if (trace_proof) die ("too many arguments");
      else if (!dimacs_file) dimacs_file = stdin, dimacs_name = "<stdin>";
      else trace_proof = 1, assert (!proof_name);
#ifndef NDEBUG
    } else if (!strcmp (argv[i], "-s")) {
      if (++i == argc) die ("argument to '-s' missing");
      if (solution_file) die ("multiple solution files");
      if (!(solution_file = fopen (argv[i], "r")))
        die ("can not read solution file '%s'", argv[i]);
      solution_name = argv[i];
#endif
    } else if (!strcmp (argv[i], "-n")) set_option ("--no-witness");
    else if (!strcmp (argv[i], "-q")) set_option ("--quiet");
    else if (!strcmp (argv[i], "-v")) set_option ("--verbose");
    else if (set_option (argv[i])) { /* nothing do be done */ }
    else if (argv[i][0] == '-') die ("invalid option '%s'", argv[i]);
    else if (trace_proof) die ("too many arguments");
    else if (dimacs_file) trace_proof = 1, proof_name = argv[i];
    else {
      if (has_suffix (argv[i], ".bz2"))
        dimacs_file = read_pipe ("bzcat %s", argv[i]), close_input = 2;
      else if (has_suffix (argv[i], ".gz"))
        dimacs_file = read_pipe ("gunzip -c %s", argv[i]), close_input = 2;
      else if (has_suffix (argv[i], ".7z"))
        dimacs_file = read_pipe ("7z x -so %s 2>/dev/null", argv[i]),
        close_input = 2;
      else dimacs_file = fopen (argv[i], "r"), close_input = 1;
      if (!dimacs_file)
        die ("can not open and read DIMACS file '%s'", argv[i]);
      dimacs_name = argv[i];
    }
  }
  if (!dimacs_file) dimacs_name = "<stdin>", dimacs_file = stdin;
  banner ();
  init_signal_handlers ();

  section ("parsing input");
  msg ("reading DIMACS file from '%s'", dimacs_name);
  parse_dimacs ();
  if (close_input == 1) fclose (dimacs_file);
  if (close_input == 2) pclose (dimacs_file);
#ifndef NDEBUG
  if (solution_file) {
    section ("parsing solution");
    msg ("reading solution file from '%s'", solution_name);
    parse_solution ();
    fclose (solution_file);
    check_satisfying_assignment (sol);
  }
#endif
  print_options ();
  section ("proof tracing");
  if (trace_proof) {
    if (proof_name) {
      if (!(proof_file = fopen (proof_name, "w")))
        die ("can not open and write DRAT proof to '%s'", proof_name);
      close_proof = 1;
    } else {
      proof_file = stdout, proof_name = "<stdout>";
      assert (!close_proof);
    }
    msg ("writing DRAT proof trace to '%s'", proof_name);
  } else msg ("will not generate nor write DRAT proof");
  res = solve ();
  if (close_proof) fclose (proof_file);
  section ("result");
  if (res == 10) {
    check_satisfying_assignment (val);
    printf ("s SATISFIABLE\n");
    if (opts.witness) print_witness ();
    fflush (stdout);
  } else {
    assert (res = 20);
    printf ("s UNSATISFIABLE\n");
    fflush (stdout);
  }
  reset_signal_handlers ();
  print_statistics ();
  reset ();
  msg ("exit %d", res);
  return res;
}
