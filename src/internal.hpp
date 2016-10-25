#ifndef _internal_hpp_INCLUDED
#define _internal_hpp_INCLUDED

#include <cassert>
#include <climits>
#include <cstdio>
#include <vector>

/*------------------------------------------------------------------------*/

using namespace std;

/*------------------------------------------------------------------------*/

#include "arena.hpp"
#include "avg.hpp"
#include "ema.hpp"
#include "flags.hpp"
#include "format.hpp"
#include "level.hpp"
#include "link.hpp"
#include "logging.hpp"
#include "options.hpp"
#include "profile.hpp"
#include "queue.hpp"
#include "stats.hpp"
#include "timer.hpp"
#include "watch.hpp"
#include "var.hpp"
#include "util.hpp"

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

class Proof;
class File;

class Internal {

  friend class Solver;

  friend class Arena;
  friend struct Logger;
  friend struct Message;
  friend class Parser;
  friend class Proof;
  friend struct Stats;

  friend struct trail_greater;
  friend struct trail_smaller;
  friend struct bump_earlier;

  /*----------------------------------------------------------------------*/

  // The actual state of the solver is in this section.

  bool unsat;                   // empty clause found or learned
  bool iterating;               // report learned unit (iteration)
  bool clashing_unit;           // found clashing units in 'parse_dimacs'
  size_t vsize;                 // actually allocated variable data size
  int max_var;                  // maximum variable index
  int level;                    // decision level ('control.size () - 1')
  signed char * vals;           // partial assignment    [-max_var,max_var]
  signed char * marks;          // literal marks         [1,max_var]
  signed char * phases;         // saved last assignment [1,max_var]
  signed char * solution;       // as vals for debugging [-max_var,max_var]
  Var * vtab;                   // variable table
  Link * ltab;                  // table of links for decision queue
  Flags * ftab;                 // seen, poison, minimized flags table
  long * btab;                  // enqueue time stamps for queue
  Queue queue;                  // variable move to front decision queue
  Watches * wtab;               // table of watches for all literals
  Clause * conflict;            // set in 'propagation', reset in 'analyze'
  size_t propagated;            // next position on trail to propagate
  vector<int> trail;            // assigned literals
  vector<int> clause;           // temporary clause in parsing & learning
  vector<int> levels;           // decision levels of 1st UIP clause
  vector<int> analyzed;         // analyzed literals in 'analyze'
  vector<int> minimized;        // marked removable or poison in 'minmize'
  vector<Level> control;        // 'level + 1 == control.size ()'
  vector<Clause*> clauses;      // ordered collection of all clauses
  vector<Clause*> resolved;     // large clauses in 'analyze'
  EMA fast_glue_avg;            // fast exponential moving average
  EMA slow_glue_avg;            // slow exponential moving average
  AVG jump_avg;                 // average back jump level
  long reduce_limit;            // conflict limit for next 'reduce'
  long restart_limit;           // conflict limit for next 'restart'
  long recently_resolved;       // to keep recently resolved clauses
  long reduce_inc;              // reduce interval increment
  long reduce_inc_inc;          // reduce interval increment increment
  long fixed_limit;             // remember last number of units
  long subsume_limit;           // next subsumption check
  size_t subsume_next;          // next clause index to try to subsume
  Proof * proof;                // trace clausal proof if non zero
  Options opts;                 // run-time options
  Stats stats;                  // statistics
  vector<int> original;         // original CNF for debugging
  vector<Timer> timers;         // active timers for profiling functions
  Profiles profiles;            // global profiled time for functions
  Arena arena;                  // memory arena for moving garbage collector
  Format error;                 // last (persistent) error message
  Internal * internal;          // proxy to 'this' in macros (redundant)

  /*----------------------------------------------------------------------*/

  // Internal delegates and helpers for corresponding functions in 'Solver'.
  //
  void resize_queue (int new_max_var);
  void resize (int new_max_var);
  void add_original_lit (int lit);

  // Enlarge tables.
  //
  void enlarge_vals (int new_vsize);
  void enlarge (int new_max_var);

  // Functions for monitoring resources.
  //
  size_t vector_bytes ();
  void inc_bytes (size_t);
  void dec_bytes (size_t);

  double seconds ();
  size_t max_bytes ();
  size_t current_bytes ();

  int active_variables () const { return max_var - stats.fixed; }

  // Regularly reports what is going on in 'report.cpp'.
  //
  void report (char type, bool verbose = false);

  // Unsigned literals (abs) with checks.
  //
  int vidx (int lit) const {
    int idx;
    assert (lit), assert (lit != INT_MIN);
    idx = abs (lit);
    assert (idx <= max_var);
    return idx;
  }

  // Unsigned version with LSB denoting sign.  This is used in indexing arrays
  // by literals.  The idea is to keep the elements in such an array for both
  // the positive and negated version of a literal close together.
  //
  unsigned vlit (int lit) { return (lit < 0) + 2u * (unsigned) vidx (lit); }

  // Helper functions to access variable and literal data.
  //
  Var & var (int lit)         { return vtab[vidx (lit)]; }
  Link & link (int lit)       { return ltab[vidx (lit)]; }
  Flags & flags (int lit)     { return ftab[vidx (lit)]; }

  const Flags & flags (int lit) const { return ftab[vidx (lit)]; }
  bool seen (int lit) const { return flags (lit).seen (); }

  Watches & watches (int lit) { return wtab[vlit (lit)]; }

  // Marking variables with a sign (positive or negative).
  //
  signed char marked (int lit) const {
    signed char res = marks [ vidx (lit) ];
    if (lit < 0) res = -res;
    return res;
  }
  void mark (int lit) {
    assert (!marked (lit));
    marks[vidx (lit)] = sign (lit);
  }
  void unmark (int lit) { marks [ vidx (lit) ] = 0; }

  // Watch literal 'lit' in clause with blocking literal 'blit'.
  // Inlined here, since it occurs in the tight inner loop of 'propagate'.
  //
  inline void watch_literal (int lit, int blit, Clause * c, int size) {
    Watches & ws = watches (lit);
    ws.push_back (Watch (blit, c, size));
    LOG (c, "watch %d blit %d in", lit, blit);
  }

  void unwatch_literal (int lit, Clause * c);

  // Update queue to point to last potentially still unassigned variable.
  // All variables after 'queue.unassigned' in bump order are assumed to be
  // assigned.  Then update the 'queue.bumped' field and and log it.  This
  // is inlined here since it occurs in several inner loops.
  //
  inline void update_queue_unassigned (int idx) {
    assert (0 < idx), assert (idx <= max_var);
    queue.unassigned = idx;
    queue.bumped = btab[idx];
    LOG ("queue unassigned now %d bumped %ld", idx, btab[idx]);
  }

  // Managing clauses in 'clause.cpp'.  Without explicit 'Clause' argument
  // these functions work on the global temporary 'clause'.
  //
  void watch_clause (Clause *);
  size_t bytes_clause (int size);
  Clause * new_clause (bool red, int glue = 0);
  void deallocate_clause (Clause *);
  void delete_clause (Clause *);
  bool tautological_clause ();
  void add_new_original_clause ();
  Clause * new_learned_clause (int glue);

  // Forward reasoning through propagation in 'propagate.cpp'.
  //
  void assign (int lit, Clause * reason = 0, int other = 0);
  bool propagate ();

  // Undo and restart in 'backtrack.cpp'.
  //
  void unassign (int lit);
  void backtrack (int target_level = 0);

  // Learning from conflicts in 'analyze.cc'.
  //
  void learn_empty_clause ();
  void learn_unit_clause (int lit);
  bool minimize_literal (int lit, int depth = 0);
  void minimize_clause ();
  void bump_variable (int lit);
  void bump_variables ();
  void bump_resolved_clauses ();
  void resolve_clause (Clause *);
  void clear_seen ();
  void clear_levels ();
  void analyze_literal (int lit, int & open);
  void analyze_reason (int lit, Clause *, int & open);
  void analyze ();
  void iterate ();       // for reporting learned unit clause

  // Restarting policy in 'restart.cc'.
  //
  bool restarting ();
  int reuse_trail ();
  void restart ();

  // Reducing means garbage collecting useless clauses in 'reduce.cpp'.
  //
  bool reducing ();
  void protect_reasons ();
  void unprotect_reasons ();
  int clause_contains_fixed_literal (Clause *);
  void flush_falsified_literals (Clause *);
  void mark_satisfied_clauses_as_garbage ();
  void mark_useless_redundant_clauses_as_garbage ();
  void move_clause (Clause *);
  void move_non_garbage_clauses ();
  void delete_garbage_clauses ();
  void flush_watches ();
  void setup_watches ();
  void garbage_collection ();
  void reduce ();

  // Eager backward subsumption checking of learned clauses.
  //
  bool eagerly_subsume_last_learned (Clause *);
  void eagerly_subsume_last_learned ();

  // Regular forward subsumption checking.
  //
  bool subsuming ();
  void strengthen_clause (Clause *, int);
  int subsume_check (Clause *);
  int subsume (Clause *);
  void subsume ();

  // Part on picking the next decision in 'decide.cpp'.
  //
  bool satisfied () const { return trail.size () == (size_t) max_var; }
  int next_decision_variable ();
  void decide ();

  // Main search functions in 'internal.cpp'.
  //
  int search ();                // CDCL loop
  void init_solving ();
  int solve ();

  // Built in profiling in 'profile.cpp'.
  //
  void start_profiling (Profile * p);
  void stop_profiling (Profile * p);
  void update_all_timers (double now);
  void print_profile (double now);

  // Checking solutions (see 'solution.cpp').
  //
  int sol (int lit) const;
  void check_clause ();

  void check (int (Internal::*assignment) (int) const);

  Internal ();
  ~Internal ();

  // Get the value of a literal: -1 = false, 0 = unassigned, 1 = true.
  //
  int val (int lit) const {
    assert (lit), assert (abs (lit) <= max_var);
    return vals[lit];
  }

  long & bumped (int lit) { return btab[vidx (lit)]; }

  // As 'val' but restricted to the root-level value of a literal.
  //
  int fixed (int lit) {
    int idx = vidx (lit), res = vals[idx];
    if (res && vtab[idx].level) res = 0;
    if (lit < 0) res = -res;
    return res;
  }

  // Parsing functions (handed over to 'parse.cpp').
  //
  const char * parse_dimacs (FILE *);
  const char * parse_dimacs (const char *);
  const char * parse_solution (const char *);

  // Enable and disable proof logging.
  void close_proof ();
  void new_proof (File *, bool owned = false);
};

};

#endif
