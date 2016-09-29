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
OPTION(emagluefast,    double,4e-2, 0,  1, "alpha fast learned glue") \
OPTION(emaf1,          double,1e-3, 0,  1, "alpha learned unit frequency") \
OPTION(emaf1lim,       double,   1, 0,100, "alpha unit frequency limit") \
OPTION(emainitsmoothly,  bool,   1, 0,  1, "initialize EMAs smoothly") \
OPTION(ematrail,       double,1e-5, 0,  1, "alpha trail") \
OPTION(keepglue,          int,   2, 1,1e9, "glue kept learned clauses") \
OPTION(keepsize,          int,   3, 2,1e9, "size kept learned clauses") \
OPTION(minimize,         bool,   1, 0,  1, "minimize learned clauses") \
OPTION(minimizedepth,     int,1000, 0,1e9, "recursive minimization depth") \
OPTION(quiet,            bool,   0, 0,  1, "disable all messages") \
OPTION(reduce,           bool,   1, 0,  1, "garbage collect clauses") \
OPTION(reduceinc,         int, 300, 1,1e9, "reduce limit increment") \
OPTION(reduceinit,        int,2000, 0,1e9, "initial reduce limit") \
OPTION(restart,          bool,   1, 0,  1, "enable restarting") \
OPTION(restartblock,   double, 1.4, 0, 10, "restart blocking factor (R)") \
OPTION(restartblocking,  bool,   1, 0,  1, "enable restart blocking") \
OPTION(restartblocklimit, int, 1e4, 0,1e9, "restart blocking limit") \
OPTION(restartblockmargin,double,1.2,0,10, "restart blocking margin") \
OPTION(restartemaf1,     bool,   0, 0,  1, "unit frequency based restart") \
OPTION(restartint,        int,  10, 1,1e9, "restart base interval") \
OPTION(restartmargin,  double, 1.1, 0, 10, "restart slow fast margin (1/K)") \
OPTION(reusetrail,       bool,   1, 0,  1, "enable trail reuse") \
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

struct Clause {

  long resolved;

  bool redundant; // aka 'learned' so not 'irredundant' (original)
  bool garbage;   // can be garbage collected unless it is a 'reason'
  bool reason;    // reason / antecedent clause can not be collected

  int glue;             // glue = glucose level = LBD
  int size;             // actual size of 'literals' (at least 2)

  int literals[2];      // actually of variadic 'size' in general
                        // for binary embedded reason clauses 'size == 2'
};

/*------------------------------------------------------------------------*/

struct Var {

  int level;            // decision level
  int trail;            // trail level

  bool seen;            // analyzed in 'analyze' and will be bumped
  bool poison;          // can not be removed during clause minimization
  bool removable;       // can be removed during clause minimization

  int prev, next;       // double links for decision VMTF queue
  long bumped;          // enqueue time stamp for VMTF queue

  Clause * reason;      // implication graph edge

  Var () :
    seen (false), poison (false), removable (false),
    prev (0), next (0), bumped (0)
  { }
};

/*------------------------------------------------------------------------*/

struct Watch {
  int blit;             // if blocking literal is true do not visit clause
  Clause * clause;
  Watch (int b, Clause * c) : blit (b), clause (c) { }
  Watch () { }
};

/*------------------------------------------------------------------------*/

typedef vector<Watch> Watches;          // of one literal

/*------------------------------------------------------------------------*/

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

/*------------------------------------------------------------------------*/

struct AVG {
  double value;
  long count;
  AVG () : value (0), count (0) { }
  operator double () const { return value; }
  void update (double y, const char * name);
};

/*------------------------------------------------------------------------*/

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

static int max_var, num_original_clauses; // 'm' and 'n' in 'p cnf <m> <n>'

#ifndef NDEBUG
static vector<int> original_literals;
#endif

// The following three actual range from '1' to 'max_var' (inclusively).

static Var * vars;
static signed char * vals;              // assignment
static signed char * phases;            // saved previous assignment

// These range from '2' to '2*max_var + 1' (again inclusively).
// See also 'vlit' below for the mapping of 'int' to this index.

static struct {
  Watches * watches;		// watches of long clauses
  Watches * binaries;		// watches of binary clauses
} literal;

// VMTF decision queue

static struct {
  int first, last;      // anchors (head/tail) for doubly linked list
  int assigned;         // all variables after this one are assigned
} queue;

static bool unsat;              // empty clause found or learned
static int level;               // decision level (levels.size () - 1)
static vector<Level> levels;	// 'level + 1 == levels.size ()'
static vector<int> trail;       // assigned literals

static struct {
  size_t binaries;    // next literal position on trail for binaries
  size_t watches;     // next literal position on trail for watches
} next;

static vector<int> clause;      // temporary clause in parsing & learning
static vector<Clause*> clauses; // ordered collection of all clauses
static bool iterating;          // report top-level assigned variables

static struct {
  vector<int> literals;         // seen & bumped literals in 'analyze'
  vector<int> levels;           // decision levels of 1st UIP clause
  vector<int> minimized;        // marked removable or poison in 'minmize'
} seen;

static vector<Clause*> resolved; // large clauses in 'analyze'
static Clause * conflict;        // set in 'propagation', reset in 'analyze'
static bool clashing_unit;       // set in 'parse_dimacs'

static struct {
  long conflicts;
  long decisions;
  long propagations;            // propagated literals in 'propagate'

  struct {
    long count;		// actual number of happened restarts 
    long tried;		// number of tried restarts
    long unit;          // from those the number forced by low unit frequency
    long blocked;       // blocked restart intervals in 'analyze'
    long unforced;      // not forced (slow glue > fast glue)
    long forced;        // forced (slow glue < fast glue)
    long reused;        // number of time trail was (partially) reused
  } restart;

  long reports, sections;

  long bumped;                  // seen and bumped variables in 'analyze'
  long resolved;                // resolved redundant clauses in 'analyze'
  long searched;                // searched decisions in 'decide'

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
  struct { EMA fast; AVG slow, blocking, nonblocking; } glue;
  EMA trail;
  AVG jump;
} avg;

static struct { bool enabled, exploring; } blocking;

// Limits for next restart, reduce.

static struct {
  struct { long conflicts, resolved; int fixed; } reduce;
  struct { long conflicts; } restart;
  long blocking;
} limits;

// Increments for next restart, reduce interval.

static struct {
  long reduce, blocking;
  double unit;
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

static void vrb (const char * fmt, ...) {
  va_list ap;
  if (opts.quiet) return;
  if (!opts.verbose) return;
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
      printf (" redundant glue %u resolved %ld", c->glue, c->resolved);
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
REPORT("reductions",   0, 2, stats.reduce.count) \
REPORT("restarts",     0, 4, stats.restart.count) \
REPORT("conflicts",    0, 5, stats.conflicts) \
REPORT("redundant",    0, 5, stats.clauses.redundant) \
REPORT("glue",         1, 4, avg.glue.slow) \
REPORT("irredundant",  0, 4, stats.clauses.irredundant) \
REPORT("variables",    0, 4, active_variables ()) \
REPORT("remaining",   -1, 5, percent (active_variables (), max_var)) \

#if 0

REPORT("f1",           0, 2, 10.0 * avg.frequency.unit) \
REPORT("properdec",    0, 3, relative (stats.propagations, stats.decisions)) \
REPORT("fastglue",     1, 4, avg.glue.fast) \
REPORT("trail",        1, 4, avg.trail) \

#endif

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

static inline Watches & binaries (int lit) {
  return literal.binaries[vlit (lit)];
}

static inline Var & var (int lit) { return vars [vidx (lit)]; }

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

static void assign (int lit, Clause * reason = 0) {
  int idx = vidx (lit);
  assert (!vals[idx]);
  Var & v = vars[idx];
  if (!(v.level = level)) learn_unit_clause (lit);
  v.reason = reason;
  vals[idx] = phases[idx] = sign (lit);
  assert (val (lit) > 0);
  v.trail = (int) trail.size ();
  trail.push_back (lit);
  LOG (reason, "assign %d", lit);
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
  Watches & ws = c->size == 2 ? binaries (lit) : watches (lit);
  ws.push_back (Watch (blit, c));
  LOG (c, "watch %d blit %d in", lit, blit);
}

static void watch_clause (Clause * c) {
  assert (c->size > 1);
  int l0 = c->literals[0], l1 = c->literals[1];
  watch_literal (l0, l1, c);
  watch_literal (l1, l0, c);
}

static size_t bytes_clause (int size) {
  return sizeof (Clause) + (size - 2) * sizeof (int);
}

static Clause * new_clause (bool red, int glue = 0) {
  assert (clause.size () <= (size_t) INT_MAX);
  const int size = (int) clause.size ();  assert (size >= 2);
  size_t bytes = bytes_clause (size);
  Clause * res = (Clause*) new char[bytes];
  inc_bytes (bytes);
  res->redundant = red;
  res->garbage = false;
  res->reason = false;
  res->glue = min (glue, (1<<27)-1);
  res->size = size;
  for (int i = 0; i < size; i++) res->literals[i] = clause[i];
  clauses.push_back (res);
  if (red) stats.clauses.redundant++;
  else     stats.clauses.irredundant++;
  if (++stats.clauses.current > stats.clauses.max)
    stats.clauses.max = stats.clauses.current;
  LOG (res, "new");
  return res;
}

static size_t delete_clause (Clause * c) {
  if (c->redundant)
       assert (stats.clauses.redundant),   stats.clauses.redundant--;
  else assert (stats.clauses.irredundant), stats.clauses.irredundant--;
  assert (stats.clauses.current);
  stats.clauses.current--;
  stats.reduce.clauses++;
  size_t bytes = bytes_clause (c->size);
  stats.reduce.bytes += bytes;
  trace_delete_clause (c);
  dec_bytes (bytes);
  delete [] (char*) c;
  return bytes;
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
    if (!tmp) assign (unit);
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
      const Watches & ws = binaries (-lit);
      for (size_t i = 0; i < ws.size (); i++) {
        const Watch & w = ws[i];
        const int other = w.blit;
        const int b = val (other);
        if (b < 0) conflict = w.clause;
        else if (!b) assign (other, w.clause);
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
        Clause * c = w.clause;
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

  if (conflict) { stats.conflicts++; LOG (conflict, "conflict"); }
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

static bool minimize_literal (int lit, int depth = 0) {
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
      res = minimize_literal (-other, depth+1);
  if (res) v.removable = true; else v.poison = true;
  seen.minimized.push_back (lit);
  if (!depth) LOG ("minimizing %d %s", lit, res ? "succeeded" : "failed");
  return res;
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
  LOG ("next VMTF decision variable %d", res);
  return res;
}

struct bump_earlier {
  bool operator () (int a, int b) {
    Var & u = var (a), & v = var (b);
    return u.bumped + u.trail < v.bumped + v.trail;
  }
};

static void bump_variable (int idx, int uip, Var * v) {
  if (!v->next) return;
  if (queue.assigned == idx)
    queue.assigned = v->prev ? v->prev : v->next;
  dequeue (v), enqueue (v, idx);
  v->bumped = ++stats.bumped;
  if (idx != uip && !vals[idx]) queue.assigned = idx;
  LOG ("VMTF bumped and moved to front %d", idx);
}

static void bump_and_clear_seen_variables (int uip) {
  START (bump);
  sort (seen.literals.begin (), seen.literals.end (), bump_earlier ());
  if (uip < 0) uip = -uip;
  for (size_t i = 0; i < seen.literals.size (); i++) {
    int idx = vidx (seen.literals[i]);
    Var * v = vars + idx;
    assert (v->seen);
    v->seen = false;
    bump_variable (idx, uip, v);
  }
  seen.literals.clear ();
  STOP (bump);
}

struct resolved_earlier {
  bool operator () (Clause * a, Clause * b) {
    return a->resolved < b->resolved;
  }
};

static void bump_resolved_clauses () {
  START (bump);
  sort (resolved.begin (), resolved.end (), resolved_earlier ());
  for (size_t i = 0; i < resolved.size (); i++)
    resolved[i]->resolved = ++stats.resolved;
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
  if (c->size <= opts.keepsize) return;
  if (c->glue <= opts.keepglue) return;
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
  if (stats.conflicts > limits.blocking) {
    if (blocking.exploring) {
      inc.blocking += opts.restartblocklimit;
      limits.blocking = stats.conflicts + inc.blocking;
      blocking.exploring = false;
      vrb ("average blocking glue %.2f non-blocking %.2f ratio %.2f",
        (double) avg.glue.blocking, (double) avg.glue.nonblocking,
        relative (avg.glue.blocking, avg.glue.nonblocking));
      if (avg.glue.blocking >
          opts.restartblockmargin * avg.glue.nonblocking) {
        vrb ("exploiting non-blocking until %ld conflicts", limits.blocking);
        blocking.enabled = false;
      } else {
        vrb ("exploiting blocking until %ld conflicts", limits.blocking);
        blocking.enabled = true;
      }
    } else {
      blocking.exploring = true;
      limits.blocking =
        stats.conflicts + max (inc.blocking/10, (long)opts.restartblocklimit);
      if (blocking.enabled) {
        vrb ("exploring non-blocking until %ld conflicts", limits.blocking);
        blocking.enabled = false;
      } else {
        vrb ("exploring blocking until %ld conflicts", limits.blocking);
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
    Clause * reason = conflict;
    LOG (reason, "analyzing conflict");
    resolve_clause (reason);
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
      LOG (reason, "analyzing %d reason", uip);
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
  conflict = 0;
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
    if (v.level && v.reason) v.reason->reason = true;
  }
}

static void unprotect_reasons () {
  for (size_t i = 0; i < trail.size (); i++) {
    Var & v = var (trail[i]);
    if (v.level && v.reason)
      assert (v.reason->reason), v.reason->reason = false;
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
    Clause * c = clauses[i];
    if (c->garbage) continue;
    const int tmp = clause_contains_fixed_literal (c);
         if (tmp > 0) c->garbage = true;
    else if (tmp < 0) flush_falsified_literals (c);
  }
}

struct less_usefull {
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
  for (size_t i = 0; i < clauses.size (); i++) {
    Clause * c = clauses[i];
    if (!c->redundant) continue;                // keep irredundant
    if (c->reason) continue;                    // need to keep reasons
    if (c->garbage) continue;                   // already marked
    if (c->size <= opts.keepsize) continue;     // keep small size clauses
    if (c->glue <= opts.keepglue) continue;     // keep small glue clauses
    if (c->resolved > limits.reduce.resolved) continue; // recently resolved
    stack.push_back (c);
  }
  sort (stack.begin (), stack.end (), less_usefull ());
  const size_t target = stack.size ()/2;
  for (size_t i = 0; i < target; i++) {
    LOG (stack[i], "marking useless to be collected");
    stack[i]->garbage = true;
  }
}

static void flush_watches () {
  size_t current_bytes = 0, max_bytes = 0;
  for (int idx = 1; idx <= max_var; idx++) {
    for (int sign = -1; sign <= 1; sign += 2) {
      for (int size = 2; size <= 3; size++) {
        const int lit = sign * idx;
        Watches & ws = size == 2 ? binaries (lit) : watches (lit);
	const size_t bytes = ws.capacity () * sizeof ws[0];
        max_bytes += bytes;
        if (fixed (lit)) ws = Watches ();
        else ws.clear (), current_bytes += bytes;
      }
    }
  }
  stats.bytes.watcher.current = current_bytes;
  if (max_bytes > stats.bytes.watcher.max)
    stats.bytes.watcher.max = max_bytes;
}

static void setup_watches () {
  for (size_t i = 0; i < clauses.size (); i++)
    watch_clause (clauses[i]);
}

static void garbage_collection () {
  size_t collected_bytes = 0, j = 0;
  for (size_t i = 0; i < clauses.size (); i++) {
    Clause * c = clauses[j++] = clauses[i];
    if (c->reason || !c->garbage) continue;
    collected_bytes += delete_clause (c);
    j--;
  }
  clauses.resize (j);
  LOG ("collected %ld bytes", collected_bytes);
}

static void reduce () {
  START (reduce);
  stats.reduce.count++;
  LOG ("reduce %ld resolved limit %ld",
    stats.reduce.count, limits.reduce.resolved);
  protect_reasons ();
  if (limits.reduce.fixed < stats.fixed)
    mark_satisfied_clauses_as_garbage ();
  mark_useless_redundant_clauses_as_garbage ();
  garbage_collection ();
  unprotect_reasons ();
  flush_watches ();
  setup_watches ();
  inc.reduce += opts.reduceinc;
  limits.reduce.conflicts = stats.conflicts + inc.reduce;
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
  assign (decision);
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
  inc.reduce = opts.reduceinit;
  inc.unit = opts.emaf1 ? 1.0 / opts.emaf1 : 1e-9;
  INIT_EMA (avg.glue.fast, opts.emagluefast);
  INIT_EMA (avg.frequency.unit, opts.emaf1);
  INIT_EMA (avg.trail, opts.ematrail);
  limits.blocking = inc.blocking = opts.restartblocklimit;
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
  msg ("tried:         %15ld   %10.2f    per restart",
    stats.restart.tried,
    relative (stats.restart.tried, stats.restart.count));
  msg ("reused:        %15ld   %10.2f %%  per restart",
    stats.restart.reused,
    percent (stats.restart.reused, stats.restart.count));
  msg ("blocked:       %15ld   %10.2f %%  per restart",
    stats.restart.blocked,
    percent (stats.restart.blocked, stats.restart.count));
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
  int prev = 0;
  for (int i = max_var; i; i--) {
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
  const int max_lit = 2*max_var + 1;
  NEW (vals,        signed char, max_var + 1);
  NEW (phases,      signed char, max_var + 1);
  NEW (vars,                Var, max_var + 1);
  NEW (literal.watches, Watches, max_lit + 1);
  NEW (literal.binaries,Watches, max_lit + 1);
  for (int i = 1; i <= max_var; i++) vals[i] = 0;
  for (int i = 1; i <= max_var; i++) phases[i] = -1;
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
