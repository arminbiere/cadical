/*--------------------------------------------------------------------------

CaDiCaL

Radically Simplified Conflict Driven Clause Learning Solver (CDCL)

The goal of CaDiCal is to have a minimalistic CDCL solver, which is easy
to understand and change, while at the same time not too much slower
than state of the art CDCL solvers if pre-processing is disabled.

MIT License

Copyright (c) 2016 Armin Biere, JKU.

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the "Software"),
to deal in the Software without restriction, including without limitation
the rights to use, copy, modify, merge, publish, distribute, sublicense,
and/or sell copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR
OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
OTHER DEALINGS IN THE SOFTWARE.

--------------------------------------------------------------------------*/

#define OPTIONS \
/*  NAME,                TYPE, VAL,LOW,HIGH,DESCRIPTION */ \
OPTION(emagluefast,    double,3e-2, 0,  1, "alpha fast learned glue") \
OPTION(emaglueslow,    double,1e-5, 0,  1, "alpha slow learned glue") \
OPTION(emajump,        double,1e-6, 0,  1, "alpha jump") \
OPTION(emaresolved,    double,1e-6, 0,  1, "alpha resolved glue & size") \
OPTION(keepglue,          int,   2, 1,1e9, "glue kept learned clauses") \
OPTION(keepsize,          int,   3, 2,1e9, "size kept learned clauses") \
OPTION(minimize,         bool,   1, 0,  1, "minimize learned clauses") \
OPTION(minimizedepth,     int,1000, 0,1e9, "recursive minimization depth") \
OPTION(reduce,           bool,   1, 0,  1, "garbage collect clauses") \
OPTION(reducedynamic,    bool,   1, 0,  1, "dynamic glue & size limit") \
OPTION(reduceinc,         int, 300, 1,1e9, "reduce limit increment") \
OPTION(reduceinit,        int,2000, 0,1e9, "initial reduce limit") \
OPTION(restart,          bool,   1, 0,  1, "enable restarting") \
OPTION(restartdelay,   double, 0.5, 0,  2, "delay restart level limit") \
OPTION(restartint,        int,  10, 1,1e9, "restart base interval") \
OPTION(restartmargin,  double, 0.1, 0, 10, "restart slow & fast margin") \
OPTION(reusetrail,       bool,   1, 0,  1, "enable trail reuse") \
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

// Type declarations

struct Clause {
  bool redundant;       // so not 'irredundant' and on 'redundant' stack
  bool garbage;         // can be garbage collected
  bool reason;          // reason clause can not be collected
  int size;             // actual size of 'literals' (at least 2)
  int literals[2];      // actually of variadic 'size'

  // Actually, a redundant clause has two additional fields
  //
  //  long resolved;      // conflict index when last resolved
  //  int glue;           // LBD = glucose level = glue
  //
  // These are however placed before the actual clause data and
  // thus not directly visible.

  static const size_t GLUE_OFFSET      =  4; // wrt '&Clause.redundant'
  static const size_t RESOLVED_OFFSET  = 12; // ditto
  static const size_t REDUNDANT_OFFSET = 12; // ditto

  long & resolved () {
    assert (this), assert (redundant);
    return *(long*) (((char*)this) - RESOLVED_OFFSET);
  }

  int & glue () {
    assert (this), assert (redundant);
    return *(int*) (((char*)this) - GLUE_OFFSET);
  }
};


struct Var {
  bool seen;            // in 'analyze'
  bool minimized;       // can be minimized in 'minimize'
  bool poison;          // can not be minimized in 'minimize'
  int mark;		// used in 'minmize_literal'

  long bumped;          // enqueue/bump time stamp for VMTF queue
  int prev, next;       // double links for decision VMTF queue

  Clause * reason;      // assignment reason/antecedent
  int level;            // decision level

  Var () :
    seen (false), minimized (false), poison (false), mark (0),
    bumped (0), prev (0), next (0)
  { }
};

struct Watch {
  int blit;             // if blocking literal is true do not visit clause
  int size;             // if size==2 no need to visit clause at all
  Clause * clause;
  Watch (int b, Clause * c) : blit (b), size (c->size), clause (c) { }
  Watch () { }
};

typedef vector<Watch> Watches;          // of one literal

struct Level {
  int decision;         // decision literal of level
  int seen;             // how man variables seen during 'analyze'
  Level (int d) : decision (d), seen (0) { }
  Level () { }
};

// We have a more complex generic exponential moving average struct here
// for more robust initialization (see documentation before 'update').

struct EMA {
  double value;         // current average value
  double alpha;         // percentage contribution of new values
  double beta;          // current upper approximation of alpha
  long wait;            // count-down using 'beta' instead of 'alpha'
  long period;          // length of current waiting phase
  EMA (double a = 0) :
     value (0), alpha (a), beta (1), wait (0), period (0)
  {
    assert (0 <= alpha), assert (alpha <= 1);
  }
  operator double () const { return value; }
  void update (double y, const char * name);
};

#ifdef PROFILING

struct Timer {
  double started;       // starting time (in seconds) for this phase
  double * update;      // update this profile if phase stops
  Timer (double s, double * u) : started (s), update (u) { }
  Timer () { }
};

#endif

/*------------------------------------------------------------------------*/

// Static variables

static int max_var, num_original_clauses;

#ifndef NDEBUG
static vector<int> original_literals;
#endif

static Var * vars;

static signed char * vals;              // assignment
static signed char * phases;            // saved previous assignment

static Watches * all_literal_watches;   // [2,2*max_var+1]

// VMTF decision queue

static struct {
  int first, last;      // anchors (head/tail) for doubly linked list
  int assigned;         // all variables after this one are assigned
} queue;

static bool unsat;              // empty clause found or learned

static int level;               // decision level (levels.size () - 1)
static vector<Level> levels;

static size_t propagate_next;   // BFS index into 'trail'
static vector<int> trail;       // assigned literals

static vector<int> clause;      // temporary clause in parsing & learning

static vector<Clause*> irredundant;     // original / not redundant clauses
static vector<Clause*> redundant;       // redundant / learned clauses

static bool iterating;          // report top-level assigned variables

static struct {
  vector<int> literals;		// bumped literals in 'analyze'
  vector<int> levels;		// decision levels of 1st UIP clause
  vector<int> minimized;	// in 'minimize_literal'
} seen;

static struct {
  vector<Clause *> clauses;
  vector<int> lits;
} work;

static vector<Clause*> resolved;

static Clause * conflict;       // set in 'propagation', reset in 'analyze'
static Clause clashing_unit;	// needed if input contains clashing units

static struct {
  long conflicts;
  long decisions;
  long propagations;            // propagated literals in 'propagate'

  long restarts;
  long delayed;                 // restarts
  long unforced;		// restarts
  long reused;                  // trails

  long reports, sections;

  long bumped;                  // seen and bumped variables in 'analyze'
  long resolved;                // resolved redundant clauses in 'analyze'
  long searched;                // searched decisions in 'decide'

  struct { long count, clauses, bytes; } reduce; // in 'reduce'

  struct { long learned, minimized; } literals;	 // in 'minimize_clause'

  struct { long current, max; } clauses;
  struct { size_t current, max; } bytes;
  struct { long units; } learned;

  int fixed;                    // top level assigned variables
} stats;

#ifdef PROFILING
static vector<Timer> timers;
#endif

// Exponential moving averages to control which clauses are collected
// in 'reduce' and when to force and delay 'restart' respectively.

static struct { 
  struct { EMA glue, size; } resolved;
  struct { struct { EMA fast, slow; } glue; } learned;
  EMA jump;
} ema;

// Limits for next restart, reduce.

static struct {
  struct { long conflicts, resolved; int fixed; } reduce;
  struct { long conflicts; } restart;
} limits;

// Increments for next restart, reduce interval.

static struct {
  struct { long conflicts; } reduce;
} inc;

static FILE * input_file, * dimacs_file, * proof_file;
static const char *input_name, *dimacs_name, *proof_name;
static int lineno, close_input, close_proof, trace_proof;

#ifndef NDEBUG

// Sam Buss suggested to debug the case where a solver incorrectly
// claims the formula to be unsatisfiable by checking every learned
// clause to be satisfied by a satisfying assignment.  Thus the first
// inconsistent learned clause will be immediately flagged without the
// need to generate proof traces and perform forward proof checking.
// The incorrectly derived clause will raise an abort signal and
// thus allows to debug the issue with a symbolic debugger immediately.

static FILE * solution_file;
static const char *solution_name;
static signed char * solution;          // like 'vals' (and 'phases')

#endif

/*------------------------------------------------------------------------*/

// Signal handlers for printing statistics even if solver is interrupted.

static bool catchedsig = false;

static void (*sig_int_handler)(int);
static void (*sig_segv_handler)(int);
static void (*sig_abrt_handler)(int);
static void (*sig_term_handler)(int);
static void (*sig_bus_handler)(int);

/*------------------------------------------------------------------------*/

static double relative (double a, double b) { return b ? a / b : 0; }

static double percent (double a, double b) { return relative (100 * a, b); }

static double seconds () {
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

static void inc_bytes (size_t bytes) {
  if ((stats.bytes.current += bytes) > stats.bytes.max)
    stats.bytes.max = stats.bytes.current;
}

static void dec_bytes (size_t bytes) {
  assert (stats.bytes.current >= bytes);
  stats.bytes.current -= bytes;
}

#define ADJUST_MAX_BYTES(V) \
  res += V.capacity () * sizeof (V[0])

static size_t max_bytes () {
  size_t res = stats.bytes.max;
#ifndef NDEBUG
  ADJUST_MAX_BYTES (original_literals);
#endif
  ADJUST_MAX_BYTES (clause);
  ADJUST_MAX_BYTES (trail);
  ADJUST_MAX_BYTES (seen.literals);
  ADJUST_MAX_BYTES (seen.levels);
  ADJUST_MAX_BYTES (seen.minimized);
  ADJUST_MAX_BYTES (resolved);
  ADJUST_MAX_BYTES (irredundant);
  ADJUST_MAX_BYTES (redundant);
  ADJUST_MAX_BYTES (levels);
  ADJUST_MAX_BYTES (work.clauses);
  ADJUST_MAX_BYTES (work.lits);
  res += (4 * stats.clauses.max * sizeof (Watch)) / 3;  // estimate
  return res;
}

static int active_variables () { return max_var - stats.fixed; }

/*------------------------------------------------------------------------*/

static void msg (const char * fmt, ...) {
  va_list ap;
  fputs ("c ", stdout);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void section (const char * title) {
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
    if (c->redundant) printf (" redundant glue %d", c->glue ());
    else printf (" irredundant");
    printf (" size %d clause", c->size);
    for (int i = 0; i < c->size; i++)
      printf (" %d", c->literals[i]);
  } else if (level) printf (" decision");
  else printf (" unit");
  fputc ('\n', stdout);
  fflush (stdout);
}

static void LOGCLAUSE (const char *fmt, ...) {
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
#define LOGCLAUSE(ARGS...) do { } while (0)
#endif

/*------------------------------------------------------------------------*/

// You might want to turn on profiling with './configure -p'.

#ifdef PROFILING

static void start (double * u) { timers.push_back (Timer (seconds (), u)); }

static void stop (double * u) {
  assert (!timers.empty ());
  const Timer & t = timers.back ();
  assert (u == t.update), (void) u;
  *t.update += seconds () - t.started;
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

static void print_profile (double all) {
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
  for (i = 0; i < size - 1; i++) {
    for (size_t j = i + 1; j < size; j++)
      if (profs[j].value > profs[i].value)
        swap (profs[i].value, profs[j].value),
        swap (profs[i].name, profs[j].name);
    msg ("%12.2f %7.2f%% %s",
      profs[i].value, percent (profs[i].value, all), profs[i].name);
  }
  msg ("  ===============================");
  msg ("%12.2f %7.2f%% all", all, 100.0);
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

  // However, we used the upper approximation 'beta' of 'alpha'.  The idea
  // is that 'beta' slowly moves down to 'alpha' to smoothly initialize
  // the exponential moving average.  This technique was used in 'Splatz'.

  // We maintain 'beta = 2^-period' until 'beta < alpha' and then set
  // it to 'alpha'.  The period gives the number of updates this 'beta'
  // is used.  So for smaller and smaller 'beta' we wait exponentially
  // longer until 'beta' is halfed again.  The sequence of 'beta's is
  //
  //   1,
  //   1/2, 1/2,
  //   1/4, 1/4, 1/4, 1/4
  //   1/8, 1/8, 1/8, 1/8, 1/8, 1/8, 1/8, 1/8,
  //   ...
  //
  //  We did not derive this formally, but observed it during logging.
  //  This is in 'Splatz' but not published yet, e.g., was not in POS'15.

  if (beta <= alpha || wait--) return;
  wait = period = 2*(period + 1) - 1;
  beta *= 0.5;
  if (beta < alpha) beta = alpha;
  LOG ("new %s EMA wait = period = %ld, beta = %g", name, wait, beta);
}

// Short hand for better logging.

#define UPDATE_EMA(E,Y) E.update ((Y), #E)

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

static int val (int lit) {
  int idx = vidx (lit), res = vals[idx];
  if (lit < 0) res = -res;
  return res;
}

// As 'val' but restricted to the root-level value of a literal.

static int fixed (int lit) {
  int idx = vidx (lit), res = vals[idx];
  if (res && vars[idx].level) res = 0;
  if (lit < 0) res = -res;
  return res;
}

// Sign of an integer, but also does proper index checking.

static int sign (int lit) {
  assert (lit), assert (abs (lit) <= max_var);
  return lit < 0 ? -1 : 1;
}

static Watches & watches (int lit) {
  int idx = vidx (lit);
  return all_literal_watches[2*idx + (lit < 0)];
}

static Var & var (int lit) { return vars [vidx (lit)]; }

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
  fputs ("0\n", proof_file);
}

static void trace_unit_clause (int unit) {
  if (!proof_file) return;
  LOG ("tracing unit clause %d", unit);
  fprintf (proof_file, "%d 0\n", unit);
}

static void trace_clause (Clause * c, bool add) {
  if (!proof_file) return;
  LOG (c, "tracing %s", add ? "addition" : "deletion");
  if (!add) fputs ("d ", proof_file);
  for (int i = 0; i < c->size; i++)
    fprintf (proof_file, "%d ", c->literals[i]);
  fputs ("0\n", proof_file);
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
  if (trail.size () < propagate_next) propagate_next = trail.size ();
  levels.resize (target_level + 1);
  level = target_level;
}

/*------------------------------------------------------------------------*/

static void watch_literal (int lit, int blit, Clause * c) {
  watches (lit).push_back (Watch (blit, c));
  LOG (c, "watch %d blit %d in", lit, blit);
}

static Clause * watch_clause (Clause * c) {
  assert (c->size > 1);
  int l0 = c->literals[0], l1 = c->literals[1];
  watch_literal (l0, l1, c);
  watch_literal (l1, l0, c);
  return c;
}

static size_t bytes_clause (bool redundant, int size) {
  assert (size >= 2);
  size_t res = sizeof (Clause) + (size - 2) * sizeof (int);
  if (redundant) res += Clause::REDUNDANT_OFFSET;
  return res;
}

static Clause * new_clause (bool red, int glue = 0) {
  assert (clause.size () <= (size_t) INT_MAX);
  int size = (int) clause.size ();
  size_t bytes = bytes_clause (red, size);
  char * ptr = new char[bytes];
  inc_bytes (bytes);
  if (red) ptr += Clause::REDUNDANT_OFFSET;
  Clause * res = (Clause*) ptr;
  res->redundant = red;
  res->garbage = false;
  res->reason = false;
  res->size = size;
  if (red) {
    res->resolved () = ++stats.resolved;
    res->glue () = glue;
  }
  for (int i = 0; i < size; i++) res->literals[i] = clause[i];
  if (red) redundant.push_back (res);
  else irredundant.push_back (res);
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
    if (lit != prev) clause[j++] = lit;
  }
  clause.resize (j);
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
      if (!unsat) msg ("parsed clashing unit"), conflict = &clashing_unit;
      else LOG ("original clashing unit produces another inconsistency");
    } else LOG ("original redundant unit");
  } else watch_clause (new_clause (false));
}

static Clause * new_learned_clause (int glue) {
  return watch_clause (new_clause (true, glue));
}

static void delete_clause (Clause * c) { 
  LOG (c, "delete");
  assert (stats.clauses.current > 0);
  stats.clauses.current--;
  dec_bytes (bytes_clause (c->redundant, c->size));
  char * ptr = (char*) c;
  if (c->redundant) ptr -= Clause::REDUNDANT_OFFSET;
  delete [] (char*) ptr;
}

/*------------------------------------------------------------------------*/

static void report (char type) {
  if (!stats.reports++)
    fputs (
"c                               redundant     irredundant            resolved\n"
"c     seconds     MB conflicts  clauses   jump   clauses variables  glue  size\n"
"c\n", stdout);
//   123456.89 123456 123456789 12345678 123456 123456789 123456789 12345 12345
  printf (
    "c %c " 
    "%9.2f " "%6.0f "   "%9ld "   "%8ld %6.0f "  "%9ld "   "%9d"  " %5.0f %5.0f\n",
    type,   
    seconds (),
    max_bytes ()/(double)(1<<20),
                  stats.conflicts,
                      (long) redundant.size (),
                               (double) ema.jump,
                                      (long) irredundant.size (),
                                                   active_variables (),
                                                        (double) ema.resolved.glue,
                                                            (double) ema.resolved.size);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/

static bool propagate () {
  assert (!unsat);
  START (propagate);
  while (!conflict && propagate_next < trail.size ()) {
    stats.propagations++;
    int lit = trail[propagate_next++];
    assert (val (lit) > 0);
    LOG ("propagating %d", lit);
    Watches & ws = watches (-lit);
    size_t i = 0, j = 0;
    while (!conflict && i < ws.size ()) {
      const Watch w = ws[j++] = ws[i++];
      const int b = val (w.blit), size = w.size;
      if (b > 0) continue;
      else if (size == 2) {
        if (b < 0) conflict = w.clause;
        else assign (w.blit, w.clause);
      } else {
        assert (w.clause->size == size);
        int * lits = w.clause->literals;
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
            LOG (w.clause, "unwatch %d in", -lit);
            swap (lits[1], lits[k]);
            watch_literal (lits[1], -lit, w.clause);
            j--;
          } else if (!u) assign (lits[0], w.clause);
          else conflict = w.clause;
        }
      }
    }
    while (i < ws.size ()) ws[j++] = ws[i++];
    ws.resize (j);
  }
  STOP (propagate);
  if (conflict) { stats.conflicts++; LOG (conflict, "conflict"); }
  return !conflict;
}

/*------------------------------------------------------------------------*/

static int minimize_literal_base_case (int root, int lit) {
  assert (val (root) > 0), assert (val (lit) > 0);
  Var & v = var (lit);
  if (!v.level || v.minimized || (root != lit && v.seen)) return 1;
  if (!v.reason || v.poison || levels[v.level].seen < 2) return -1;
  return 0;
}

#if 0

static bool minimize_literal (int root, int lit = 0, int depth = 0) {
  if (!lit) lit = root;
  Var & v = var (lit);
  const int tmp = minimize_literal_base_case (root, lit);
  if (tmp > 0) return true; else if (tmp < 0) return false;
  if (depth++ > opts.minimizedepth) return false;
  bool res = true;
  for (int i = 0; res && i < v.reason->size; i++) {
    int other = v.reason->literals[i];
    if (other != lit) res = minimize_literal (root, -other, depth + 1);
  }
  if (res) v.minimized = true; else v.poison = true;
  seen.minimized.push_back (lit);
  if (!depth) LOG ("minimizing %d %s", root, res ? "succeeded" : "failed");
  return res;
}

#else

static bool minimize_literal (int root) {
  assert (val (root) > 0);
  assert (work.lits.empty ());
  work.lits.push_back (root);
  while (!work.lits.empty ()) {
    int lit = work.lits.back ();
    assert (val (lit) > 0);
    if (minimize_literal_base_case (root, lit)) work.lits.pop_back ();
    else {
      Var & v = var (lit);
      assert (!v.minimized), assert (!v.poison);
      if (v.mark < v.reason->size) {
	assert (v.mark >= 0);
	int other = v.reason->literals[v.mark];
	if (other == lit) v.mark++;
	else {
	  const int tmp = minimize_literal_base_case (root, -other);
	  if (tmp < 0) {
	    v.poison = true;
	    seen.minimized.push_back (lit);
            work.lits.pop_back ();
	  } else if (tmp > 0) v.mark++;
	  else work.lits.push_back (-other);
	}
      } else {
	assert (v.mark == v.reason->size);
	assert (!v.poison);
        work.lits.pop_back ();
	v.minimized = true;
	seen.minimized.push_back (lit);
      }
    }
  }
  const int tmp = minimize_literal_base_case (root, root);
  assert (tmp == -1 || tmp == 1);
  const bool res = tmp > 0;
  LOG ("minimizing %d %s", root, res ? "succeeded" : "failed");
  return res;
}

#endif

static void minimize_clause () {
  if (!opts.minimize) return;
  START (minimize);
  LOGCLAUSE ("minimizing");
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
    v.minimized = v.poison = false;
    v.mark = 0;
  }
  seen.minimized.clear ();
  STOP (minimize);
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
  return res;
}

struct bumped_earlier {
  bool operator () (int a, int b) {
    return var (a).bumped < var (b).bumped;
  }
};

static void bump_and_clear_seen_variables (int uip) {
  START (bump);
  sort (seen.literals.begin (), seen.literals.end (), bumped_earlier ());
  if (uip < 0) uip = -uip;
  for (size_t i = 0; i < seen.literals.size (); i++) {
    int idx = vidx (seen.literals[i]);
    Var * v = vars + idx;
    assert (v->seen);
    v->seen = false;
    if (!v->next) continue;
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
    levels[seen.levels[i]].seen = 0;
  seen.levels.clear ();
}

static void resolve_clause (Clause * c) { 
  if (!c->redundant) return;
  UPDATE_EMA (ema.resolved.size, c->size);
  UPDATE_EMA (ema.resolved.glue, c->glue ());
  if (c->size <= opts.keepsize) return;
  if (c->glue () <= opts.keepglue) return;
  resolved.push_back (c);
}

static bool analyze_literal (int lit) {
  Var & v = var (lit);
  if (v.seen) return false;
  if (!v.level) return false;
  assert (val (lit) < 0);
  if (v.level < level) clause.push_back (lit);
  if (!levels[v.level].seen++) {
    LOG ("found new level %d contributing to conflict");
    seen.levels.push_back (v.level);
  }
  v.seen = true;
  seen.literals.push_back (lit);
  LOG ("analyzed literal %d assigned at level %d", lit, v.level);
  return v.level == level;
}

struct level_greater_than {
  bool operator () (int a, int b) { return var (a).level > var (b).level; }
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
    LOG (reason, "analyzing conflicting");
    resolve_clause (reason);
    int open = 0, uip = 0;
    size_t i = trail.size ();
    for (;;) {
      for (int j = 0; j < reason->size; j++)
        if (analyze_literal (reason->literals[j])) open++;
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
    int size = (int) clause.size ();
    int glue = (int) seen.levels.size ();
    UPDATE_EMA (ema.learned.glue.slow, glue);
    UPDATE_EMA (ema.learned.glue.fast, glue);
    LOG ("original 1st UIP clause of size %d and glue %d", size, glue);
    if (opts.minimize) minimize_clause (), check_clause ();
    Clause * driving_clause = 0;
    int jump = 0;
    if (size == 1) {
      LOG ("learned unit clause %d", -uip); 
      stats.learned.units++;
    } else {
      sort (clause.begin (), clause.end (), level_greater_than ());
      assert (clause[0] == -uip);
      driving_clause = new_learned_clause (glue);
      trace_add_clause (driving_clause);
      jump = var (clause[1]).level;
      assert (jump < level);
    }
    UPDATE_EMA (ema.jump, jump);
    backtrack (jump);
    assign (-uip, driving_clause);
    bump_and_clear_seen_variables (uip);
    clause.clear ();
    clear_levels ();
  }
  conflict = 0;
  STOP (analyze);
}

static bool satisfied () { return trail.size () == (size_t) max_var; }

/*------------------------------------------------------------------------*/

static bool restarting () {
  if (!opts.restart) return false;
  if (stats.conflicts <= limits.restart.conflicts) return false;
  limits.restart.conflicts = stats.conflicts + opts.restartint;
  double s = ema.learned.glue.slow, f = ema.learned.glue.fast;
  double l = (1.0 + opts.restartmargin) * s;
  LOG ("EMA learned glue slow %.2f fast %.2f limit %.2f", s, f, l);
  if (l > f) { stats.unforced++; LOG ("unforced"); return false; }
  double j = ema.jump; l = opts.restartdelay * j;
  LOG ("EMA jump %.2f limit %.2f", j, l);
  if (level < l) { stats.delayed++; LOG ("delayed"); return false; }
  return true;
}

static int reusetrail () {
  if (!opts.reusetrail) return 0;
  long limit = var (next_decision_variable ()).bumped;
  int res = 0;
  while (res < level && var (levels[res + 1].decision).bumped > limit)
    res++;
  if (res) { stats.reused++; LOG ("reusing trail %d", res); }
  return res;
}

static void restart () {
  START (restart);
  stats.restarts++;
  LOG ("restart %ld", stats.restarts);
  backtrack (reusetrail ());
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
static bool clause_root_level_satisfied (Clause * c) {
  for (int i = 0; i < c->size; i++)
    if (fixed (c->literals[i]) > 0) return true;
  return false;
}

static void mark_satisfied_clauses_as_garbage (const vector<Clause*> & cs) {
  for (size_t i = 0; i < cs.size (); i++)
    if (clause_root_level_satisfied (cs[i])) cs[i]->garbage = true;
}

static void mark_useless_redundant_clauses_as_garbage () {
  work.clauses.clear ();
  for (size_t i = 0; i < redundant.size (); i++) {
    Clause * c = redundant[i];
    assert (c->redundant);
    if (c->reason) continue;
    if (c->garbage) continue;
    if (c->size <= opts.keepsize) continue;
    if (c->glue () <= opts.keepglue) continue;
    if (c->resolved () > limits.reduce.resolved) continue;
    if (opts.reducedynamic &&
        c->glue () < ema.resolved.glue &&
        c->size    < ema.resolved.size) continue;
    work.clauses.push_back (c);
  }
  sort (work.clauses.begin (), work.clauses.end (), resolved_earlier ());
  const size_t target = work.clauses.size ()/2;
  for (size_t i = 0; i < target; i++)
    work.clauses[i]->garbage = true;
}

static void unprotect_reasons () {
  for (size_t i = 0; i < trail.size (); i++) {
    Var & v = var (trail[i]);
    if (v.level && v.reason)
      assert (v.reason->reason), v.reason->reason = false;
  }
}

static void flush_watches () {
  for (int idx = 1; idx <= max_var; idx++) {
    if (fixed (idx)) 
      watches (idx) = Watches (), watches (-idx) = Watches ();
    else {
      for (int sign = -1; sign <= 1; sign += 2) {
        Watches & ws = watches (sign * idx);
        const size_t size = ws.size ();
        size_t i = 0, j = 0;
        while (i < size) {
          Watch w = ws[j++] = ws[i++];
          if (w.clause->garbage) j--;
        }
        ws.resize (j);
      }
    }
  }
}

static void collect_garbage_clauses (vector<Clause*> & clauses) {
  const size_t size = clauses.size ();
  size_t i = 0, j = 0;
  while (i < size) {
    Clause * c = clauses[j++] = clauses[i++];
    if (c->reason || !c->garbage) continue;
    stats.reduce.clauses++;
    stats.reduce.bytes += bytes_clause (c->redundant, c->size);
    trace_delete_clause (c);
    delete_clause (c);
    j--;
  }
  clauses.resize (j);
}

static void reduce () {
  START (reduce);
  stats.reduce.count++;
  LOG ("reduce %ld", stats.reduce.count);
  protect_reasons ();
  const bool new_units = (limits.reduce.fixed < stats.fixed);
  if (new_units) 
    mark_satisfied_clauses_as_garbage (irredundant),
    mark_satisfied_clauses_as_garbage (redundant);
  mark_useless_redundant_clauses_as_garbage ();
  flush_watches ();
  if (new_units) collect_garbage_clauses (irredundant);
  collect_garbage_clauses (redundant);
  unprotect_reasons ();
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
  inc.reduce.conflicts = opts.reduceinit/2;
  INIT_EMA (ema.learned.glue.fast, opts.emagluefast);
  INIT_EMA (ema.learned.glue.slow, opts.emaglueslow);
  INIT_EMA (ema.resolved.glue, opts.emaresolved);
  INIT_EMA (ema.resolved.size, opts.emaresolved);
  INIT_EMA (ema.jump, opts.emajump);
}

static int solve () {
  init_solving ();
  section ("solving");
  return search ();
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
    stats.restarts, relative (stats.conflicts, stats.restarts));
  msg ("reused:        %15ld   %10.2f %%  per restart",
    stats.reused, percent (stats.reused, stats.restarts));
  msg ("delayed:       %15ld   %10.2f %%  per restart",
    stats.delayed, percent (stats.delayed, stats.restarts));
  msg ("unforced:      %15ld   %10.2f %%  per restart",
    stats.unforced, percent (stats.unforced, stats.restarts));
  msg ("units:         %15ld   %10.2f    conflicts per unit",
    stats.learned.units, relative (stats.conflicts, stats.learned.units));
  msg ("bumped:        %15ld   %10.2f    per conflict",
    stats.bumped, relative (stats.bumped, stats.conflicts));
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
  for (int i = max_var; i >= 1; i--) {
    Var * v = &vars[i];
    if ((v->prev = prev)) var (prev).next = i;
    else queue.first = i;
    v->bumped = ++stats.bumped;
    prev = i;
  }
  queue.last = queue.assigned = prev;
}

static void reset_signal_handlers (void) {
  (void) signal (SIGINT, sig_int_handler);
  (void) signal (SIGSEGV, sig_segv_handler);
  (void) signal (SIGABRT, sig_abrt_handler);
  (void) signal (SIGTERM, sig_term_handler);
  (void) signal (SIGBUS, sig_bus_handler);
}

static void catchsig (int sig) {
  if (!catchedsig) {
    catchedsig = true;
    msg ("CAUGHT SIGNAL %d", sig);
    msg ("s UNKNOWN");
    print_statistics ();
  }
  reset_signal_handlers ();
  msg ("RERAISING SIGNAL %d", sig);
  raise (sig);
}

static void init_signal_handlers (void) {
  sig_int_handler = signal (SIGINT, catchsig);
  sig_segv_handler = signal (SIGSEGV, catchsig);
  sig_abrt_handler = signal (SIGABRT, catchsig);
  sig_term_handler = signal (SIGTERM, catchsig);
  sig_bus_handler = signal (SIGBUS, catchsig);
}

#define NEW(P,T,N) \
  P = new T[N], inc_bytes ((N) * sizeof (T))

static void init_variables () {
  NEW (vals, signed char, max_var + 1);
  NEW (phases, signed char, max_var + 1);
  NEW (vars, Var, max_var + 1);
  NEW (all_literal_watches, Watches, 2 * (max_var + 1));
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
  for (size_t i = 0; i < irredundant.size (); i++)
    delete_clause (irredundant[i]);
  for (size_t i = 0; i < redundant.size (); i++)
    delete_clause (redundant[i]);
  delete [] all_literal_watches;
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
  int res = getc (input_file);
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
      while ((ch = getc (solution_file)) != '\n')
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
    if (!c) fputc ('v', stdout), c = 1;
    char str[20];
    sprintf (str, " %d", val (i) < 0 ? -i : i);
    int l = strlen (str);
    if (c + l > 78) fputs ("\nv", stdout), c = 1;
    fputs (str, stdout);
    c += l;
  }
  if (c) fputc ('\n', stdout);
  fputs ("v 0\n", stdout);
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
    else if (set_option (argv[i])) { /* nothing do be done */ }
    else if (argv[i][0] == '-') die ("invalid option '%s'", argv[i]);
    else if (trace_proof) die ("too many arguments");
    else if (dimacs_file) trace_proof = 1, proof_name = argv[i];
    else {
      if (has_suffix (argv[i], ".bz2"))
        dimacs_file = read_pipe ("bzcat %s", argv[i]), close_input = 2;
      else if (has_suffix (argv[i], ".gz"))
        dimacs_file = read_pipe ("gunzip -c %s", argv[i]), close_input = 2;
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
