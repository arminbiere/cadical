#ifndef _solver_hpp_INCLUDED
#define _solver_hpp_INCLUDED

#include <cassert>
#include <climits>
#include <vector>

/*------------------------------------------------------------------------*/

using namespace std;

#include "macros.hpp"
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
#include "queue.hpp"
#include "report.hpp"

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

class Solver {
  
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
  Queue queue;
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

#ifndef NDEBUG

#endif

  Proof * proof;

  Options opts;
  Stats stats;

  /*------------------------------------------------------------------------*/

  void init_variables ();

  size_t vector_bytes ();
  void inc_bytes (size_t);
  void dec_bytes (size_t);

  int active_variables () const { return max_var - stats.fixed; }

  void report (char type, bool verbose = false);

  int vidx (int lit) {
    int idx;
    assert (lit), assert (lit != INT_MIN);
    idx = abs (lit);
    assert (idx <= max_var);
    return idx;
  }

  // Unsigned version with LSB denoting sign.  This is used in indexing arrays
  // by literals.  The idea is to keep the elements in such an array for both
  // the positive and negated version of a literal close together.

  unsigned vlit (int lit) {
    return (lit < 0) + 2u * (unsigned) vidx (lit);
  }

  Var & var (int lit) { return vars [vidx (lit)]; }
  Watches & watches (int lit) { return literal.watches[vlit (lit)]; }
  Watches & binaries (int lit) { return literal.binaries[vlit (lit)]; }

  void watch_literal (int lit, int blit, Clause * c) {
    Watches & ws = c->size == 2 ? binaries (lit) : watches (lit);
    ws.push_back (Watch (blit, c));
#ifdef LOGGING
    Solver * solver = this;
    LOG (c, "watch %d blit %d in", lit, blit);
#endif
  }

  void watch_clause (Clause * c) {
    assert (c->size > 1);
    int l0 = c->literals[0], l1 = c->literals[1];
    watch_literal (l0, l1, c);
    watch_literal (l1, l0, c);
  }

  size_t bytes_clause (int size);
  Clause * new_clause (bool red, int glue = 0);
  size_t delete_clause (Clause *);
  bool tautological_clause ();
  void add_new_original_clause ();
  Clause * new_learned_clause (int glue);

  void learn_empty_clause ();
  void learn_unit_clause (int lit);

  void assign (int lit, Clause * reason = 0);
  void unassign (int lit);
  void backtrack (int target_level = 0);

  bool propagate ();

  bool minimize_literal (int lit, int depth = 0);
  void minimize_clause ();

  void bump_variable (Var * v, int uip);
  void bump_and_clear_seen_variables (int uip);

  void bump_resolved_clauses ();
  void resolve_clause (Clause *);
  void clear_levels ();
  bool analyze_literal (int);
  void analyze ();
  void iterate ();

  bool restarting ();
  bool blocking_enabled ();
  int reuse_trail ();
  void restart ();

  bool reducing ();
  void protect_reasons ();
  void unprotect_reasons ();
  int clause_contains_fixed_literal (Clause *);
  void flush_falsified_literals (Clause *);
  void mark_satisfied_clauses_as_garbage ();
  void mark_useless_redundant_clauses_as_garbage ();
  void flush_watches ();
  void setup_watches ();
  void garbage_collection ();
  void reduce ();

  bool satisfied () const { return trail.size () == (size_t) max_var; }
  int next_decision_variable ();
  void decide ();

  int search ();
  void init_solving ();
  int solve ();

#ifdef PROFILING
  vector<Timer> timers;
  Profiles profiles;
  void start_profiling (double * p);
  void stop_profiling (double * p);
  void update_all_timers (double now);
  void print_profile (double now);
#endif

#ifndef NDEBUG
  // Sam Buss suggested to debug the case where a solver incorrectly claims
  // the formula to be unsatisfiable by checking every learned clause to be
  // satisfied by a satisfying assignment.  Thus the first inconsistent
  // learned clause will be immediately flagged without the need to generate
  // proof traces and perform forward proof checking.  The incorrectly derived
  // clause will raise an abort signal and thus allows to debug the issue with
  // a symbolic debugger immediately.
  signed char * solution;          // like 'vals' (and 'phases')
  int sol (int lit);
  void check_clause ();
#endif

  Solver * solver;		// proxy to 'this' in macros

  friend class Parser;
  friend struct Logger;
  friend struct Message;
  friend struct Stats;
  friend struct Signal;
  friend struct Queue;
  friend class App;

  friend struct trail_smaller_than;
  friend struct trail_greater_than;
  friend struct bump_earlier;

public:
  
  Solver ();
  ~Solver ();

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
  size_t current_bytes ();
};

};

#endif
