#ifndef _cadical_hpp_INCLUDED
#define _cadical_hpp_INCLUDED

#include <vector>

using namespace std;

#include <climits>
#include <cassert>

#include "options.hpp"
#include "clause.hpp"
#include "var.hpp"
#include "watch.hpp"
#include "ema.hpp"
#include "avg.hpp"
#include "level.hpp"
#include "timer.hpp"
#include "parse.hpp"
#include "proof.hpp"
#include "profiles.hpp"
#include "logging.hpp"
#include "file.hpp"
#include "message.hpp"
#include "stats.hpp"
#include "util.hpp"
#include "signal.hpp"

namespace CaDiCaL {

class Solver {

  friend class Parser;
  friend struct Logger;
  friend struct Message;
  friend struct Stats;
  friend struct Signal;

  Options opts;
  int max_var;
  int num_original_clauses;
  vector<int> original_literals;
  Var * vars;
  signed char * vals;
  signed char * phases;

  struct {
    Watches * watches;		// watches of long clauses
    Watches * binaries;		// watches of binary clauses
  } literal;

  // VMTF decision queue

  struct {
    int first, last;    // anchors (head/tail) for doubly linked list
    int assigned;       // all variables after this one are assigned
  } queue;

  bool unsat;           // empty clause found or learned
  int level;            // decision level (levels.size () - 1)
  vector<Level> levels; // 'level + 1 == levels.size ()'
  vector<int> trail;    // assigned literals

  struct {
    size_t binaries;    // next literal position on trail for binaries
    size_t watches;     // next literal position on trail for watches
  } next;

  vector<int> clause;      // temporary clause in parsing & learning
  vector<Clause*> clauses; // ordered collection of all clauses
  bool iterating;          // report top-level assigned variables

  struct {
    vector<int> literals;  // seen & bumped literals in 'analyze'
    vector<int> levels;    // decision levels of 1st UIP clause
    vector<int> minimized; // marked removable or poison in 'minmize'
  } seen;

  vector<Clause*> resolved; // large clauses in 'analyze'
  Clause * conflict;        // set in 'propagation', reset in 'analyze'
  bool clashing_unit;       // set in 'parse_dimacs'

  Stats stats;

  // Averages to control which clauses are collected in 'reduce' and when to
  // force and delay 'restart' respectively.  Most of them are exponential
  // moving average, but for the slow glue we use an actual average.

  struct {
    struct { EMA unit; } frequency;
    struct { EMA fast; AVG slow, blocking, nonblocking; } glue;
    EMA trail;
    AVG jump;
  } avg;

  struct { bool enabled, exploring; } blocking;

  // Limits for next restart, reduce.

  struct {
    struct { long conflicts, resolved; int fixed; } reduce;
    struct { long conflicts; } restart;
    long blocking;
  } limits;

  // Increments for next restart, reduce interval.

  struct {
    long reduce, blocking;
    double unit;
  } inc;

  // Sam Buss suggested to debug the case where a solver incorrectly claims
  // the formula to be unsatisfiable by checking every learned clause to be
  // satisfied by a satisfying assignment.  Thus the first inconsistent
  // learned clause will be immediately flagged without the need to generate
  // proof traces and perform forward proof checking.  The incorrectly derived
  // clause will raise an abort signal and thus allows to debug the issue with
  // a symbolic debugger immediately.

  signed char * solution;          // like 'vals' (and 'phases')

  Proof * proof;

  // In essence 'abs' but also checks whether 'lit' is a valid literal.

  int vidx (int lit) {
    int idx;
    assert (lit), assert (lit != INT_MIN);
    idx = abs (lit);
    assert (idx <= max_var);
    return idx;
  }

  // Unsigned version with LSB denoting sign.  This is used in indexing arrays
  // by literals.  The idea is to keep the elements in such an array for both
  // the positive and negated version of a literal close together

  unsigned vlit (int lit) {
    return (lit < 0) + 2u * (unsigned) vidx (lit);
  }

  Watches & watches (int lit) {
    return literal.watches[vlit (lit)];
  }

  Watches & binaries (int lit) {
    return literal.binaries[vlit (lit)];
  }

  Var & var (int lit) { return vars [vidx (lit)]; }

  void init_variables ();
  bool tautological ();
  void add_new_original_clause ();

#ifdef PROFILING
  vector<Timer> timers;
  Profiles profiles;

  void start_profiling (double * p);
  void stop_profiling (double * p);

#define START(P) solver.start_profiling (&solver.profiles.P)
#define STOP(P) solver.stop_profiling (&solver.profiles.P)

#else

#define START(P) do { } while (0)
#define STOP(P) do { } while (0)

#endif

#define NEW(P,T,N) \
  do { (P) = new T[N], solver.inc_bytes ((N) * sizeof (T)); } while (0)

  void inc_bytes (size_t);
  void dec_bytes (size_t);

public:

  // Get the value of a literal: -1 = false, 0 = unassigned, 1 = true.

  int val (int lit) {
    int idx = vidx (lit), res = vals[idx];
    if (lit < 0) res = -res;
    return res;
  }

  // As 'val' but restricted to the root-level value of a literal.

  int fixed (int lit) {
    int idx = vidx (lit), res = vals[idx];
    if (res && vars[idx].level) res = 0;
    if (lit < 0) res = -res;
    return res;
  }

  double seconds ();
  size_t max_bytes ();
};

};

#endif
