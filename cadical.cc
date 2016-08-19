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
#include <climits>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <csignal>

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
  Watch (int b, Clause * c) :
    blit (b), size (c->size), clause (c)
  { }
  Watch () { }		// needed for 'vector'
};

typedef vector<Watch> Watches;		// of one literal

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
static signed char * vals;			// assignment
static signed char * phases;
static Watches * all_literal_watches;

// VMTF decision queue

static struct {
  Var * first, * last;	// anchors (head/tail) for doubly linked list
  Var * assigned;	// all variables after this one are assigned
} queue;

static bool unsat;		// empty clause found or learned
static int level;		// decision level;
static size_t propagate_next;	// BFS index into 'trail'
static vector<int> literals;	// temporary clause in parsing & learning
static vector<int> trail;	// assigned literals
static vector<int> seen;	// seen literals in 'analyze'

static vector<Clause*> irredundant;	// all not redundant clauses
static vector<Clause*> redundant;	// all redundant clauses

static Clause * conflict;	// set in 'propagation', reset in 'analyze'

static struct {
  long conflicts;
  long decisions;
  long restarts;
  long propagations;
  long bumped;
  struct { long current, max; } clauses;
  struct { size_t current, max; } bytes;
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

static FILE * input, * proof;
static int close_input, close_proof;
static const char * input_name, * proof_name;

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
  ADJUST_MAX_BYTES (seen);
  ADJUST_MAX_BYTES (irredundant);
  ADJUST_MAX_BYTES (redundant);
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
  msg ("---- [ run-time profiling data ] -------------------");
  msg ("");
  PRINT_PROFILE (analyze);
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

#if 0
static Clause * new_learned_clause (int g) {
  return watch_clause (new_clause (true, g));
}
#endif

static void delete_clause (Clause * c) { 
  LOG (c, "delete");
  assert (stats.clauses.current > 0);
  stats.clauses.current--;
  dec_bytes (bytes_clause (c->size));
  delete [] (char*) c;
}

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

static void trace_empty_clause () {
  if (!proof) return;
  LOG ("trace empty clause");
  fputs ("0\n", proof);
}

static void analyze () {
  assert (conflict);
  if (!level) {
    assert (!unsat);
    msg ("learned empty clause");
    trace_empty_clause ();
    unsat = true;
  }
  START (analyze);
  STOP (analyze);
}

static bool satisfied () { return trail.size () == (size_t) max_var; }

static bool restarting () {
  if (stats.conflicts <= limits.restart.conflicts) return false;
  return 1.25 * ema.learned.glue.fast  > ema.learned.glue.slow;
}

static void restart () {
  START (restart);
  stats.restarts++;
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
  while (val (queue.assigned - vars))
    queue.assigned = queue.assigned->prev;
  int idx = queue.assigned - vars;
  int decision = phases[idx] * idx;
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

static void print_statistics () {
  double t = seconds ();
  size_t m = max_bytes ();
  print_profile (t);
  msg ("");
  msg ("---- [ statistics ] --------------------------------");
  msg ("");
  msg ("conflicts:     %20ld   %10.2f  (per second)",
    stats.conflicts, relative (stats.conflicts, t));
  msg ("decisions:     %20ld   %10.2f  (per second)",
    stats.decisions, relative (stats.decisions, t));
  msg ("restarts:      %20ld   %10.2f  (per second)",
    stats.restarts, relative (stats.restarts, t));
  msg ("propagations:  %20ld   %10.2f  (per second)",
    stats.propagations, relative (stats.propagations, t));
  msg ("maxbytes:      %20ld   %10.2f  MB",
    m, m/(double)(1<<20));
  msg ("time:          %20s   %10.2f  seconds", "", t);
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

static void init () {
  NEW (vals, signed char, max_var + 1);
  NEW (phases, signed char, max_var + 1);
  NEW (vars, Var, max_var + 1);
  NEW (all_literal_watches, Watches, 2 * (max_var + 1));
  for (int i = 1; i <= max_var; i++) vals[i] = 0;
  for (int i = 1; i <= max_var; i++) phases[i] = -1;
  init_vmtf_queue ();
  msg ("initialized %d variables", max_var);
  init_signal_handlers ();
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
"usage: cadical [ -h ] [ <input> [ <proof> ] ]\n"
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

static void parse_dimacs () {
  int ch;
  START (parse);
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
    DEBUG (original_literals.push_back (lit));
    if (lit) {
      if (literals.size () == INT_MAX) die ("clause too large");
      literals.push_back (lit);
    } else {
      if (!tautological ()) add_new_original_clause ();
      else LOG ("tautological original clause");
      literals.clear ();
      if (parsed_clauses++ >= num_original_clauses) die ("too many clauses");
    }
  }
  if (lit) die ("last clause without '0'");
  if (parsed_clauses < num_original_clauses) die ("clause missing");
  msg ("parsed %d clauses in %.2f seconds", parsed_clauses, seconds ());
  STOP (parse);
}

static void check_witness () {
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
  banner ();
  msg ("");
  msg ("reading DIMACS file from '%s'", input_name);
  if (proof) msg ("writing DRAT proof to '%s'", proof_name);
  else msg ("will not generate nor write DRAT proof");
  parse_dimacs ();
  if (close_input == 1) fclose (input);
  if (close_input == 2) pclose (input);
  res = search ();
  if (close_proof) fclose (proof);
  msg ("");
  if (res == 10) {
    printf ("s SATISFIABLE\n");
    check_witness ();
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
