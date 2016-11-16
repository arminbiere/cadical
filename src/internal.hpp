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
#include "clause.hpp"
#include "ema.hpp"
#include "flags.hpp"
#include "format.hpp"
#include "inc.hpp"
#include "level.hpp"
#include "limit.hpp"
#include "link.hpp"
#include "logging.hpp"
#include "occs.hpp"
#include "options.hpp"
#include "profile.hpp"
#include "queue.hpp"
#include "stats.hpp"
#include "timer.hpp"
#include "util.hpp"
#include "var.hpp"
#include "watch.hpp"

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

#ifdef LOGGING
  friend struct AVG;
  friend struct EMA;
  friend class Options;
#endif

  friend struct bumped_earlier;
  friend struct less_noccs;
  friend struct trail_bumped_smaller;
  friend struct trail_smaller;

  /*----------------------------------------------------------------------*/

  // The actual state of the solver is in this section.

  bool unsat;                   // empty clause found or learned
  bool iterating;               // report learned unit (iteration)
  bool clashing;                // found clashing units in during parsing
  bool simplifying;		// outside of CDCL loop
  size_t vsize;                 // actually allocated variable data size
  int max_var;                  // maximum variable index
  int level;                    // decision level ('control.size () - 1')
  signed char * vals;           // assignment       [-max_var,max_var]
  signed char * solution;       // for debugging    [-max_var,max_var]
  signed char * marks;          // signed marks     [1,max_var]
  signed char * phases;         // saved assignment [1,max_var]
  unsigned char * etab;         // eliminated table
  Var * vtab;                   // variable table
  Link * ltab;                  // table of links for decision queue
  Flags * ftab;                 // seen, poison, minimized flags table
  long * btab;                  // enqueue time stamps for queue
  Queue queue;                  // variable move to front decision queue
  Occs * otab;                  // table of occurrences for all literals
  long * ntab;                  // table number irredundant occurrences
  long * ttab;                  // touched variable table
  Watches * wtab;               // table of watches for all literals
  Clause * conflict;            // set in 'propagation', reset in 'analyze'
  size_t propagated;            // next trail position to propagate
  vector<int> trail;            // assigned literals
  vector<int> clause;           // temporary in parsing & learning
  vector<int> levels;           // decision levels in learned clause
  vector<int> analyzed;         // analyzed literals in 'analyze'
  vector<int> minimized;        // removable or poison in 'minimize'
  vector<int> original;         // original CNF for debugging
  vector<int> extension;        // original CNF for debugging
  vector<Level> control;        // 'level + 1 == control.size ()'
  vector<Clause*> clauses;      // ordered collection of all clauses
  vector<Clause*> resolved;     // resolved clauses in 'analyze' & 'elim'
  vector<Timer> timers;         // active timers for profiling functions
  EMA fast_glue_avg;            // fast glue average
  EMA slow_glue_avg;            // slow glue average
  EMA restartint;               // actual restart interval average
  EMA restarteff;               // restart effectiveness average
  EMA size_avg;                 // learned clause size average
  EMA jump_avg;                 // jump average
  Limit lim;                    // limits for various phases
  Inc inc;                      // limit increments
  Proof * proof;                // trace clausal proof if non zero
  Options opts;                 // run-time options
  Stats stats;                  // statistics
  Profiles profiles;            // global profiled time for functions
  Arena arena;                  // memory arena for moving garbage collector
  Format error;                 // last (persistent) error message
  Internal * internal;          // proxy to 'this' in macros (redundant)
  File * output;                // output file

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
  void inc_bytes (size_t);
  void dec_bytes (size_t);

  double seconds ();
  size_t max_bytes ();
  size_t current_bytes ();

  size_t bytes_occs ();
  size_t bytes_watches ();
  void account_implicitly_allocated_bytes ();
  void update_max_bytes ();

  int active_variables () const {
    return max_var - stats.fixed - stats.eliminated;
  }

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
  long & bumped (int lit)     { return btab[vidx (lit)]; }
  long & touched (int lit)    { return ttab[vlit (lit)]; }

  const Flags & flags (int lit) const { return ftab[vidx (lit)]; }

  const bool occs () const { return otab != 0; }
  const bool watches () const { return wtab != 0; }

  Occs & occs (int lit) { assert (otab); return otab[vlit (lit)]; }
  long & noccs (int lit) { assert (ntab); return ntab[vlit (lit)]; }
  Watches & watches (int lit) { assert (wtab); return wtab[vlit (lit)]; }

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

  void mark_clause ();          // mark 'this->clause'
  void unmark_clause ();        // unmark 'this->clause'

  void mark (Clause *);
  void unmark (Clause *);

  // Watch literal 'lit' in clause with blocking literal 'blit'.
  // Inlined here, since it occurs in the tight inner loop of 'propagate'.
  //
  inline void watch_literal (int lit, int blit, Clause * c, int size) {
    Watches & ws = watches (lit);
    ws.push_back (Watch (blit, c, size));
    LOG (c, "watch %d blit %d in", lit, blit);
  }

  // Update queue to point to last potentially still unassigned variable.
  // All variables after 'queue.unassigned' in bump order are assumed to be
  // assigned.  Then update the 'queue.bumped' field and log it.  This is
  // inlined here since it occurs in several inner loops.
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
  void touch_clause (Clause *);
  void mark_garbage (Clause *);
  bool tautological_clause ();
  void add_new_original_clause ();
  Clause * new_learned_redundant_clause (int glue);
  Clause * new_resolved_irredundant_clause ();

  // Forward reasoning through propagation in 'propagate.cpp'.
  //
  void assign (int lit);                 // unit or decision
  void assign (int lit, Clause *);       // driving learned clause
  void assign (int lit, Clause *, int);  // inlined in 'propagate.cpp'
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
  bool shrink_literal (int lit, int depth = 0);
  void shrink_clause ();
  void bump_variable (int lit);
  void bump_variables ();
  void bump_analyzed_clauses ();
  void analyze_clause (Clause *);
  void clear_seen ();
  void clear_levels ();
  void clear_minimized ();
  void analyze_literal (int lit, int & open);
  void analyze_reason (int lit, Clause *, int & open);
  void analyze ();
  void iterate ();       // for reporting learned unit clause

  // Restarting policy in 'restart.cc'.
  //
  bool restarting ();
  int reuse_trail ();
  void restart ();

  // Asynchronous terminating check.
  //
  bool terminating ();
  void terminate ();            // TODO: not implemented yet.

  // Reducing means determining useless clauses with 'reduce' in
  // 'reduce.cpp' as well as root level satisfied clause and then removing
  // those which are not used as reason anymore with garbage collection.
  //
  bool reducing ();
  void protect_reasons ();
  void mark_useless_redundant_clauses_as_garbage ();
  void unprotect_reasons ();
  void reduce ();

  // Garbage collection called from 'reduce' and during preprocessing.
  //
  int clause_contains_fixed_literal (Clause *);
  void remove_falsified_literals (Clause *);
  void mark_satisfied_clauses_as_garbage ();
  void move_clause (Clause *);
  void flush_watches (int lit);
  size_t flush_occs (int lit);
  void flush_all_occs_and_watches ();
  void move_non_garbage_clauses ();
  void delete_garbage_clauses ();
  void check_clause_stats ();
  void garbage_collection ();

  // Eager backward subsumption checking of learned clauses.
  //
  bool eagerly_subsume_last_learned (Clause *);
  void eagerly_subsume_last_learned ();

  // Set-up occurrence list counters and containers.
  //
  void init_occs ();
  void init_noccs ();
  void init_watches ();
  void connect_watches ();
  void reset_occs ();
  void reset_noccs ();
  void reset_watches ();

  // Regular forward subsumption checking.
  //
  bool subsuming ();
  void strengthen_clause (Clause *, int);
  void subsume_clause (Clause * subsuming, Clause * subsumed);
  int subsume_check (Clause * subsuming, Clause * subsumed);
  int try_to_subsume_clause (Clause *, bool, long);
  bool subsume_round (bool irredundant_only = false);
  void subsume ();

  // Bounded variable elimination.
  //
  bool eliminating ();
  bool resolve_clauses (Clause * c, int pivot, Clause * d);
  void mark_eliminated_clauses_as_garbage (int pivot);
  bool resolvents_are_bounded (int pivot);
  void add_resolvents (int pivot);
  void elim_variable (int pivot);
  bool elim_round ();
  void extend ();
  void elim ();

  // Failed literal probing.
  //
  bool occurs_in_binary_clauses (int lit);
  bool probing ();
  void probe ();

  // Part on picking the next decision in 'decide.cpp'.
  //
  bool satisfied () const { return trail.size () == (size_t) max_var; }
  int next_decision_variable ();
  void assume_decision (int decision);
  void decide ();

  // Main search functions in 'internal.cpp'.
  //
  int search ();                // CDCL loop
  void init_solving ();
  int solve ();

  // Built in profiling in 'profile.cpp'.
  //
  void start_profiling (Profile * p, double);
  void stop_profiling (Profile * p, double);

  void start_profiling (Profile * p) { start_profiling (p, seconds ()); }
  void stop_profiling (Profile * p) { stop_profiling (p, seconds ()); }

  void update_all_timers (double now);
  void print_profile (double now);

  // Checking solutions (see 'solution.cpp').
  //
  int sol (int lit) const;
  void check_shrunken_clause (Clause *);
  void check_learned_clause ();

  void check (int (Internal::*assignment) (int) const);

  Internal ();
  ~Internal ();

  // Get the value of a literal: -1 = false, 0 = unassigned, 1 = true.
  // We use a redundant table for both negative and positive literals.  This
  // however allows a branch-less check for the value of literal and is
  // considered substantially faster than negating the result if the
  // argument is negative.  We also avoid taking the absolute value.
  //
  int val (int lit) const {
    assert (lit), assert (abs (lit) <= max_var);
    return vals[lit];
  }

  // As 'val' but restricted to the root-level value of a literal.
  // It is not that time critical and also needs to check the decision level
  // of the variable anyhow.
  //
  int fixed (int lit) {
    int idx = vidx (lit), res = vals[idx];
    if (res && vtab[idx].level) res = 0;
    if (lit < 0) res = -res;
    return res;
  }

  unsigned char & eliminated (int lit) { return etab [vidx (lit) ]; }

  // Parsing functions (handed over to 'parse.cpp').
  //
  const char * parse_dimacs (FILE *);
  const char * parse_dimacs (const char *);
  const char * parse_solution (const char *);

  // Enable and disable proof logging.
  //
  void close_proof ();
  void new_proof (File *, bool owned = false);

  // Dump to '<stdout>' as DIMACS mostly for debugging.
  //
  void dump ();
};

/*------------------------------------------------------------------------*/

struct trail_smaller {
  Internal * internal;
  trail_smaller (Internal * s) : internal (s) { }
  bool operator () (int a, int b) {
    return internal->var (a).trail < internal->var (b).trail;
  }
};

};

#endif
