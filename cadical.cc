/*--------------------------------------------------------------------------

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

// Type declarations

struct Clause {
  bool redundant;	// so not 'irredundant' and on 'redudant' stack
  bool garbage;		// can be garbage collected
  int size;		// actual size of 'literals'
  int glue;		// LBD = glucose level = glue
  long resolved;	// conflict index when last resolved
  int literals[1];	// actually of variadic 'size'
};

struct Var {
  bool seen;		// in 'analyze'
  bool minimized;	// can be minimized in 'minimize'
  bool poison;		// can not be minimized in 'minimize'
  int level;		// decision level

  long bumped;		// enqueue/bump time stamp for VMTF queue
  Var * prev, * next;	// double links for decision VMTF queue

  Clause * reason;	// assignment reason/antecedent

  Var () :
    seen (false), minimized (false), poison (false),
    bumped (0), prev (0), next (0)
  { }
};

struct Watch {
  int blit;		// if blocking literal is true do not visit clause
  int size;		// if size==2 no need to visit clause at all
  Clause * clause;
  Watch (int b, Clause * c) : blit (b), size (c->size), clause (c) { }
  Watch () { }
};

typedef vector<Watch> Watches;		// of one literal

struct Level {
  int decision;		// decision literal of level
  int seen;		// how man variables seen during 'analyze'
  Level (int d) : decision (d), seen (0) { }
  Level () { }
};

#ifdef PROFILE

struct Timer {
  double started;	// starting time (in seconds) for this phase
  double * update;	// update this profile if phase stops
  Timer (double s, double * u) : started (s), update (u) { }
};

#endif

/*------------------------------------------------------------------------*/

// Static variables

static int max_var, num_original_clauses;

#ifndef NDEBUG
static vector<int> original_literals;
#endif

static Var * vars;

static signed char * vals;		// assignment
static signed char * phases;		// saved previous assignment
static signed char * solution;		// for debugging

static Watches * all_literal_watches;	// [2,2*max_var+1]

// VMTF decision queue

static struct {
  Var * first, * last;	// anchors (head/tail) for doubly linked list
  Var * next;		// all variables after this one are assigned
} queue;

static bool unsat;		// empty clause found or learned

static int level;		// decision level (levels.size () - 1)
static vector<Level> levels;

static size_t propagate_next;	// BFS index into 'trail'
static vector<int> trail;	// assigned literals

static vector<int> literals;	// temporary clause in parsing & learning

static vector<Clause*> irredundant;	// all not redundant clauses
static vector<Clause*> redundant;	// all redundant clauses

static struct {
  vector<int> literals, levels;	// seen literals & levels in 'analyze'
} seen;

static Clause * conflict;	// set in 'propagation', reset in 'analyze'

static struct {
  long conflicts;
  long decisions;
  long restarts;
  long propagations;
  long bumped;
  struct { long current, max; } clauses;
  struct { size_t current, max; } bytes;
  struct { long units; } learned;
} stats;

#ifdef PROFILE
static vector<Timer> timers;
#endif

static struct { 
  struct { double glue, size; } resolved;
  struct { struct { double fast, slow; } glue; } learned;
} ema;

static struct {
  struct { long conflicts; } restart, reduce;
} limits;

static FILE * input_file, * proof_file, * solution_file;
static const char * input_name, * proof_name, * solution_name;
static int lineno = 1, close_input, close_proof;

static bool catchedsig = false;

static void (*sig_int_handler)(int);
static void (*sig_segv_handler)(int);
static void (*sig_abrt_handler)(int);
static void (*sig_term_handler)(int);
static void (*sig_bus_handler)(int);

/*------------------------------------------------------------------------*/

#ifdef NDEBUG
#define DEBUG(ARGS...) do { } while (0)
#else
#define DEBUG(CODE) do { CODE; } while (0)
#endif

static double relative (double a, double b) { return b ? a / b : 0; }

#ifdef PROFILE
static double percent (double a, double b) { return relative (100 * a, b); }
#endif

static void update_ema (double & ema, double y, double alpha) {
  ema += alpha * (y - ema);
}

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
  ADJUST_MAX_BYTES (literals);
  ADJUST_MAX_BYTES (trail);
  ADJUST_MAX_BYTES (seen.literals);
  ADJUST_MAX_BYTES (seen.levels);
  ADJUST_MAX_BYTES (irredundant);
  ADJUST_MAX_BYTES (redundant);
  ADJUST_MAX_BYTES (levels);
  res += (4 * stats.clauses.max * sizeof (Watch)) / 3;	// estimate
  return res;
}

static void msg (const char * fmt, ...) {
  va_list ap;
  fputs ("c ", stdout);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
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
  } else if (level) printf (" decision");
  else printf (" unit");
  fputc ('\n', stdout);
  fflush (stdout);
}

#else
#define LOG(ARGS...) do { } while (0)
#endif

/*------------------------------------------------------------------------*/

#ifdef PROFILE

static void start (double * u) { timers.push_back (Timer (seconds (), u)); }

static void stop (double * u) {
  assert (!timers.empty ());
  const Timer & t = timers.back ();
  assert (u == t.update), (void) u;
  *t.update += seconds () - t.started;
  timers.pop_back ();
}

static struct { 
  double analyze;
  double bump;
  double decide;
  double parse;
  double propagate;
  double reduce;
  double restart;
  double search;
} profile;

#define START(P) start (&profile.P)
#define STOP(P) stop (&profile.P)

#define PRINT_PROFILE(P) \
  msg ("%12.2f %7.2f%% %s", profile.P, percent (profile.P, all), #P)

static void print_profile (double all) {
  msg ("");
  msg ("---- [ run-time profiling data ] ------------------------");
  msg ("");
  PRINT_PROFILE (analyze);
  PRINT_PROFILE (bump);
  PRINT_PROFILE (decide);
  PRINT_PROFILE (parse);
  PRINT_PROFILE (propagate);
  PRINT_PROFILE (reduce);
  PRINT_PROFILE (restart);
  PRINT_PROFILE (search);
  msg ("  ===============================");
  msg ("%12.2f %7.2f%% all", all, 100.0);
}

#else
#define START(ARGS...) do { } while (0)
#define STOP(ARGS...) do { } while (0)
#define print_profile(ARGS...) do { } while (0)
#endif

/*------------------------------------------------------------------------*/

static int vidx (int lit) {
  int idx;
  assert (lit), assert (lit != INT_MIN);
  idx = abs (lit);
  assert (idx <= max_var);
  return idx;
}

static int val (int lit) {
  int idx = vidx (lit), res = vals[idx];
  if (lit < 0) res = -res;
  return res;
}

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

static void assign (int lit, Clause * reason = 0) {
  int idx = vidx (lit);
  assert (!vals[idx]);
  Var & v = vars[idx];
  v.level = level;
  v.reason = reason;
  vals[idx] = phases[idx] = sign (lit);
  assert (val (lit) > 0);
  trail.push_back (lit);
  LOG (reason, "assign %d", lit);
}

static void unassign (int lit, int except) {
  assert (val (lit) > 0);
  int idx = vidx (lit);
  vals[idx] = 0;
  LOG ("unassign %d", lit);
  if (lit == except) return;
  Var * v = vars + idx;
  if (queue.next->bumped >= v->bumped) return;
  queue.next = v;
  LOG ("queue next moved to %d", idx);
}

static void backtrack (int target_level, int except = 0) {
  assert (target_level <= level);
  if (target_level == level) return;
  LOG ("backtracking to decision level %d", target_level);
  int decision = levels[target_level + 1].decision, lit;
  do {
    unassign (lit = trail.back (), except);
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

static size_t bytes_clause (int size) {
  assert (size > 0);
  return sizeof (Clause) + (size - 1) * sizeof (int);
}

static Clause * new_clause (bool red, int glue = 0) {
  assert (literals.size () <= (size_t) INT_MAX);
  int size = (int) literals.size ();
  size_t bytes = bytes_clause (size);
  inc_bytes (bytes);
  Clause * res = (Clause*) new char[bytes];
  res->size = size;
  res->glue = glue;
  res->resolved = stats.conflicts;
  res->redundant = red;
  res->garbage = false;
  for (int i = 0; i < size; i++) res->literals[i] = literals[i];
  if (red) redundant.push_back (res);
  else irredundant.push_back (res);
  if (++stats.clauses.current > stats.clauses.max)
    stats.clauses.max = stats.clauses.current;
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

static Clause * new_learned_clause (int g) {
  return watch_clause (new_clause (true, g));
}

static void delete_clause (Clause * c) { 
  LOG (c, "delete");
  assert (stats.clauses.current > 0);
  stats.clauses.current--;
  dec_bytes (bytes_clause (c->size));
  delete [] (char*) c;
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

static void trace_add_clause (Clause * c) {
  if (!proof_file) return;
  LOG (c, "tracing");
  for (int i = 0; i < c->size; i++)
    fprintf (proof_file, "%d ", c->literals[i]);
  fputs ("0\n", proof_file);
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
      const int b = val (w.blit);
      if (b > 0) continue;
      else if (w.size == 2) {
	if (b < 0) conflict = w.clause;
	else assign (w.blit, w.clause);
      } else {
	assert (w.clause->size == w.size);
	int * lits = w.clause->literals;
	if (lits[1] != -lit) swap (lits[0], lits[1]);
	assert (lits[1] == -lit);
	const int u = val (lits[0]);
	if (u > 0) ws[j-1].blit = lits[0];
	else {
	  int k, v = 0;
	  for (k = 2; k < w.size && (v = val (lits[k])) < 0; k++)
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

struct bumped_earlier {
  bool operator () (int a, int b) {
    return var (a).bumped < var (b).bumped;
  }
};

static void dequeue (Var * v) {
  if (v->prev) v->prev->next = v->next; else queue.first = v->next;
  if (v->next) v->next->prev = v->prev; else queue.last = v->prev;
}

static void enqueue (Var * v) {
  if ((v->prev = queue.last)) queue.last->next = v; else queue.first = v;
  queue.last = v;
  v->next = 0;
}

static void bump_seen_literals (int uip) {
  START (bump);
  sort (seen.literals.begin (), seen.literals.end (), bumped_earlier ());
  if (uip < 0) uip = -uip;
  for (size_t i = 0; i < seen.literals.size (); i++) {
    int idx = vidx (seen.literals[i]);
    Var * v = vars + idx;
    assert (v->seen);
    v->seen = v->minimized = v->poison = false;
    if (!v->next) continue;
    queue.next = v->prev ? v->prev : v->next;
    dequeue (v), enqueue (v);
    v->bumped = ++stats.bumped;
    if (idx != uip && !vals[idx]) queue.next = v;
    LOG ("bumped and moved to front %d", idx);
  }
  STOP (bump);
  seen.literals.clear ();
  for (size_t i = 0; i < seen.levels.size (); i++)
    levels[seen.levels[i]].seen = 0;
  seen.levels.clear ();
}

struct level_greater_than {
  bool operator () (int a, int b) {
    return var (a).level > var (b).level;
  }
};

static bool analyze_literal (int lit) {
  Var & v = var (lit);
  if (v.seen) return false;
  if (!v.level) return false;
  assert (val (lit) < 0);
  if (v.level < level) literals.push_back (-lit);
  if (!levels[v.level].seen++) {
    LOG ("found new level %d contributing to conflict");
    seen.levels.push_back (v.level);
  }
  v.seen = true;
  seen.literals.push_back (lit);
  LOG ("analyzed literal %d assigned at level %d", lit, v.level);
  return v.level == level;
}

static void analyze () {
  assert (conflict);
  START (analyze);
  if (!level) {
    assert (!unsat);
    msg ("learned empty clause");
    trace_empty_clause ();
    unsat = true;
  } else {
    Clause * reason = conflict;
    LOG (reason, "analyzing conflicting");
    assert (literals.empty ());
    assert (seen.literals.empty ());
    assert (seen.levels.empty ());
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
    literals.push_back (-uip);
    int size = literals.size ();
    if (size == 1) {
      LOG ("learned unit clause %d", -uip); 
      trace_unit_clause (-uip);
      stats.learned.units++;
      backtrack (0, uip);
      assign (-uip);
    } else {
      sort (literals.begin (), literals.end (), level_greater_than ());
      assert (literals[0] == -uip);
      int glue = (int) seen.levels.size ();
      Clause * driving_clause = new_learned_clause (glue);
      update_ema (ema.learned.glue.slow, glue, 0.0001);
      update_ema (ema.learned.glue.fast, glue, 0.03);
      LOG ("new slow learned glue EMA %.4f", ema.learned.glue.slow);
      LOG ("new slow learned fast EMA %.4f", ema.learned.glue.fast);
      trace_add_clause (driving_clause);
      int jump = var (literals[1]).level;
      assert (jump < level);
      backtrack (jump, uip);
      assign (-uip, driving_clause);
    }
    bump_seen_literals (uip);
    literals.clear ();
  }
  conflict = 0;
  STOP (analyze);
}

static bool satisfied () { return trail.size () == (size_t) max_var; }

static bool restarting () {
  if (stats.conflicts <= limits.restart.conflicts) return false;
  double slow = ema.learned.glue.slow;
  double fast = ema.learned.glue.fast;
  double limit = 1.25  * slow;
  LOG ("EMA learned glue: slow %.2f, limit %.2f %c fast %.2f",
    slow, limit, (limit < fast ? '<' : (limit == fast ? '=' : '>')), fast);
  return limit < fast;
}

static void restart () {
  START (restart);
  stats.restarts++;
  limits.restart.conflicts = stats.conflicts + 50;
  STOP (restart);
}

static bool reducing () {
  return false;
}

static void reduce () {
  START (reduce);
  STOP (reduce);
}

static void decide () {
  START (decide);
  level++;
  stats.decisions++;
  int idx;
  while (val (idx = queue.next - vars))
    queue.next = queue.next->prev;
  int decision = phases[idx] * idx;
  levels.push_back (Level (decision));
  LOG ("decide %d", decision);
  assign (decision);
  STOP (decide);
}

static int search () {
  int res = 0;
  START (search);
  while (!res)
         if (unsat) res = 20;
    else if (!propagate ()) analyze ();
    else if (satisfied ()) res= 10;
    else if (restarting ()) restart ();
    else if (reducing ()) reduce ();
    else decide ();
  STOP (search);
  return res;
}

/*------------------------------------------------------------------------*/

static void print_statistics () {
  double t = seconds ();
  size_t m = max_bytes ();
  print_profile (t);
  msg ("");
  msg ("---- [ statistics ] -------------------------------------");
  msg ("");
  msg ("conflicts:     %15ld   %10.2f  (per second)",
    stats.conflicts, relative (stats.conflicts, t));
  msg ("decisions:     %15ld   %10.2f  (per second)",
    stats.decisions, relative (stats.decisions, t));
  msg ("restarts:      %15ld   %10.2f  (per second)",
    stats.restarts, relative (stats.restarts, t));
  msg ("propagations:  %15ld   %10.2f  (per second)",
    stats.propagations, relative (stats.propagations, t));
  msg ("maxbytes:      %15ld   %10.2f  MB",
    m, m/(double)(1<<20));
  msg ("time:          %15s   %10.2f  seconds", "", t);
  msg ("");
}

static void init_vmtf_queue () {
  Var * prev = 0;
  for (int i = 1; i <= max_var; i++) {
    Var * v = &vars[i];
    if ((v->prev = prev)) prev->next = v;
    else queue.first = v;
    v->bumped = ++stats.bumped;
    prev = v;
  }
  queue.last = queue.next = prev;
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

static void init_search () {
  limits.restart.conflicts = stats.conflicts + 50;
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

static const char * USAGE =
"usage: cadical [ <option> ... ] [ <input> [ <proof> ] ]\n"
"\n"
"where '<option>' is one of the following\n"
"\n"
"-h         print this command line option summary\n"
"-s <sol>   read and check solution (competition output format)\n"
"\n"
"and '<input>' is a (compressed) DIMACS file and '<output>'\n"
"is a file to store the DRAT proof.  If no '<proof>' file is\n"
"specified, then no proof is generated.  If no '<input>' is given\n"
"then '<stdin>' is used. If '-' is used as '<input>' then the\n"
"solver reads from '<stdin>'.  If '-' is specified for '<proof>'\n"
"then the proof is generated and printed to '<stdout>'.\n";

struct lit_less_than {
  bool operator () (int a, int b) {
    int res = abs (a) - abs (b);
    if (res) return res;
    return a < b ? -1 : 1;
  }
};

static bool tautological () {
  std::sort (literals.begin (), literals.end (), lit_less_than ());
  size_t j = 0;
  int prev = 0;
  for (size_t i = 0; i < literals.size (); i++) {
    int lit = literals[i];
    if (lit == -prev) return true;
    if (lit != prev) literals[j++] = lit;
  }
  literals.resize (j);
  return false;
}

static int nextch () {
  int res = getc (input_file);
  if (res == '\n') lineno++;
  return res;
}

static void parse_dimacs () {
  int ch;
  START (parse);
  for (;;) {
    ch = nextch ();
    if (ch != 'c') break;
    while ((ch = nextch ()) != '\n')
      if (ch == EOF)
	perr ("unexpected end-of-file in header comment");
  }
  if (ch != 'p') perr ("expected 'c' or 'p'");
  if (nextch () != ' ') perr ("expected ' ' after 'p'");
  if (nextch () != 'c') perr ("expected 'c' after 'p '");
  if (nextch () != 'n') perr ("expected 'n' after 'p c'");
  if (nextch () != 'f') perr ("expected 'f' after 'p cn'");
  if (nextch () != ' ') perr ("expected ' ' after 'p cnf'");
  if (!isdigit (ch = nextch ())) perr ("expected digit after 'p cnf '");
  max_var = ch - '0';
  while (isdigit (ch = nextch ())) {
    int digit = ch - '0';
    if (INT_MAX/10 < max_var || INT_MAX - digit < 10*max_var)
      perr ("too large '<max-var>' in header");
    max_var = 10*max_var + digit;
  }
  if (ch != ' ') perr ("expected ' ' after 'p cnf %d'", max_var);
  if (!isdigit (ch = nextch ()))
    perr ("expected digit after 'p cnf %d '", max_var);
  num_original_clauses = ch - '0';
  while (isdigit (ch = nextch ())) {
    int digit = ch - '0';
    if (INT_MAX/10 < num_original_clauses ||
        INT_MAX - digit < 10*num_original_clauses)
      perr ("too large '<num-clauses>' in header");
    num_original_clauses = 10*num_original_clauses + digit;
  }
  while (ch == ' ' || ch == '\r') ch = nextch ();
  if (ch != '\n') perr ("expected new-line after 'p cnf %d %d'",
                        max_var, num_original_clauses);
  msg ("found 'p cnf %d %d' header", max_var, num_original_clauses);
  init_variables ();
  int lit = 0, parsed_clauses = 0;
  while ((ch = nextch ()) != EOF) {
    if (ch == ' ' || ch == '\n' || ch == '\t' || ch == '\r') continue;
    if (ch == 'c') {
      while ((ch = nextch ()) != '\n')
	if (ch == EOF) perr ("unexpected end-of-file in body comment");
      continue;
    }
    int sign;
    if (ch == '-') {
      ch = nextch ();
      if (!isdigit (ch)) perr ("expected digit after '-'");
      sign = -1;
    } else if (!isdigit (ch))
      perr ("expected '-' or digit (or comment start character 'c')");
    else sign = 1;
    lit = ch - '0';
    while (isdigit (ch = nextch ())) {
      int digit = ch - '0';
      if (INT_MAX/10 < lit || INT_MAX - digit < 10*lit)
	perr ("too large literal in header");
      lit = 10*lit + digit;
    }
    if (lit > max_var)
      perr ("literal exceeds maximum variable index %d", max_var);
    lit *= sign;
    DEBUG (original_literals.push_back (lit));
    if (lit) {
      if (literals.size () == INT_MAX) perr ("clause too large");
      literals.push_back (lit);
    } else {
      if (!tautological ()) add_new_original_clause ();
      else LOG ("tautological original clause");
      literals.clear ();
      if (parsed_clauses++ >= num_original_clauses) perr ("too many clauses");
    }
  }
  if (lit) perr ("last clause without '0'");
  if (parsed_clauses < num_original_clauses) perr ("clause missing");
  msg ("parsed %d clauses in %.2f seconds", parsed_clauses, seconds ());
  STOP (parse);
}

static void parse_solution () {
  NEW (solution, signed char, max_var + 1);
}

static void check_produced_witness () {
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
    } else if (!satisfied && val (lit) > 0) satisfied = true;
  }
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
  msg ("CaDiCaL Radically Simplified CDCL SAT Solver");
  msg ("Version " VERSION " " GITID);
  msg ("Copyright (c) 2016 Armin Biere, JKU");
  msg (COMPILE);
}

int main (int argc, char ** argv) {
  int i, res;
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h")) fputs (USAGE, stdout), exit (0);
    else if (!strcmp (argv[i], "-s")) {
      if (solution_file) die ("multiple solution files");
      if (!(solution_file = fopen (argv[i], "r")))
	die ("can not read solution file '%s'", argv[i]);
      solution_name = argv[i];
    } else if (!strcmp (argv[i], "-")) {
      if (proof_file) die ("too many arguments");
      else if (!input_file) input_file = stdin, input_name = "<stdin>";
      else proof_file = stdout, proof_name = "<stdout>";
    } else if (argv[i][0] == '-')
    die ("invalid option '%s'", argv[i]);
    else if (proof_file) die ("too many arguments");
    else if (input_file) {
      if (!(proof_file = fopen (argv[i], "w")))
	die ("can not open and write DRAT proof to '%s'", argv[i]);
      proof_name = argv[i], close_proof = 1;
    } else {
      if (has_suffix (argv[i], ".bz2"))
	input_file = read_pipe ("bzcat %s", argv[i]), close_input = 2;
      else if (has_suffix (argv[i], ".gz"))
	input_file = read_pipe ("gunzip -c %s", argv[i]), close_input = 2;
      else input_file = fopen (argv[i], "r"), close_input = 1;
      if (!input_file)
	die ("can not open and read DIMACS file '%s'", argv[i]);
      input_name = argv[i];
    }
  }
  if (!input_file) input_name = "<stdin>", input_file = stdin;
  banner ();
  init_signal_handlers ();
  msg ("");
  if (proof_file) msg ("writing DRAT proof to '%s'", proof_name);
  else msg ("will not generate nor write DRAT proof");
  msg ("reading DIMACS file from '%s'", input_name);
  parse_dimacs ();
  if (close_input == 1) fclose (input_file);
  if (close_input == 2) pclose (input_file);
  if (solution_file) {
    msg ("reading solution file from '%s'", input_name);
    parse_solution ();
    fclose (solution_file);
  }
  init_search ();
  res = search ();
  if (close_proof) fclose (proof_file);
  msg ("");
  if (res == 10) {
    printf ("s SATISFIABLE\n");
    check_produced_witness ();
    print_witness ();
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
