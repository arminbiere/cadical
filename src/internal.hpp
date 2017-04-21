#ifndef _internal_hpp_INCLUDED
#define _internal_hpp_INCLUDED

/*------------------------------------------------------------------------*/

// Common 'C' headers.

#include <cassert>
#include <climits>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cctype>

/*------------------------------------------------------------------------*/

// Common 'C++' headers.

#include <vector>
#include <algorithm>

/*------------------------------------------------------------------------*/

#include "arena.hpp"
#include "bins.hpp"
#include "cadical.hpp"
#include "clause.hpp"
#include "elim.hpp"
#include "ema.hpp"
#include "external.hpp"
#include "file.hpp"
#include "flags.hpp"
#include "format.hpp"
#include "heap.hpp"
#include "internal.hpp"
#include "iterator.hpp"
#include "level.hpp"
#include "limit.hpp"
#include "logging.hpp"
#include "macros.hpp"
#include "mem.hpp"
#include "message.hpp"
#include "occs.hpp"
#include "options.hpp"
#include "parse.hpp"
#include "profile.hpp"
#include "proof.hpp"
#include "queue.hpp"
#include "resources.hpp"
#include "stats.hpp"
#include "util.hpp"
#include "var.hpp"
#include "watch.hpp"

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

using namespace std;

class External;
class File;

/*------------------------------------------------------------------------*/

class Internal {

  /*----------------------------------------------------------------------*/

  friend class Arena;
  friend class External;
  friend class File;
  friend struct Logger;
  friend struct Message;
  friend class Parser;
  friend class Proof;
  friend class Solver;
  friend struct Stats;

#ifdef LOGGING
  friend struct EMA;
  friend class Options;
#endif

  // Comparison functors for sorting.
  //
  friend struct bumped_earlier;
  friend struct less_negated_occs;
  friend struct less_usefull;
  friend struct more_noccs2;
  friend struct subsume_less_noccs;
  friend struct trail_bumped_smaller;
  friend struct better_watch;
  friend struct trail_larger;
  friend struct trail_assigned_smaller;
  friend struct vivify_less_clause;
  friend struct vivify_more_noccs;

  typedef signed char signed_char;

  /*----------------------------------------------------------------------*/

  // The actual state of the solver is in this section.

  bool unsat;                   // empty clause found or learned
  bool iterating;               // report learned unit (iteration)
  bool clashing;                // found clashing units in during parsing
  bool simplifying;             // simplifying thus outside of CDCL loop
  bool vivifying;               // during vivification
  size_t vsize;                 // actually allocated variable data size
  int max_var;                  // (internal) maximum variable index
  int level;                    // decision level ('control.size () - 1')
  signed char * vals;           // assignment          [-max_var,max_var]
  signed char * marks;          // signed marks        [1,max_var]
  signed char * phases;         // saved assignment    [1,max_var]
  int * i2e;			// internal idx to external lit
  Queue queue;                  // variable move to front decision queue
  Var * vtab;                   // variable table
  Link * ltab;                  // table of links for decision queue
  Flags * ftab;                 // seen, poison, minimized flags table
  long * btab;                  // enqueue time stamps for queue
  Occs * otab;                  // table of occurrences for all literals
  long * ntab;                  // table number one sided occurrences
  long * ntab2;                 // table number two sided occurrences
  int * ptab;                   // propagated table
  Bins * big;                   // binary implication graph
  Watches * wtab;               // table of watches for all literals
  Clause * conflict;            // set in 'propagation', reset in 'analyze'
  size_t propagated;            // next trail position to propagate
  size_t probagated;            // next trail position to probagate
  size_t probagated2;           // next binary trail position to probagate
  vector<int> trail;            // assigned literals
  vector<int> clause;           // temporary in parsing & learning
  vector<int> levels;           // decision levels in learned clause
  vector<int> analyzed;         // analyzed literals in 'analyze'
  vector<int> minimized;        // removable or poison in 'minimize'
  vector<int> probes;           // remaining scheduled probes
  vector<Level> control;        // 'level + 1 == control.size ()'
  vector<Clause*> clauses;      // ordered collection of all clauses
  ElimSchedule esched;          // bounded variable elimination schedule
  EMA fast_glue_avg;            // fast glue average
  EMA slow_glue_avg;            // slow glue average
  EMA size_avg;                 // learned clause size average
  EMA jump_avg;                 // jump average
  double wg, ws;
  Limit lim;                    // limits for various phases
  Inc inc;                      // limit increments
  Proof * proof;                // trace clausal proof if non zero
  Options opts;                 // run-time options
  Stats stats;                  // statistics
#ifndef QUIET
  vector<Timer> timers;         // active timers for profiling functions
  Profiles profiles;            // global profiled time for functions
#endif
  Arena arena;                  // memory arena for moving garbage collector
  Format error;                 // last (persistent) error message
  Clause binary_subsuming;      // communicate binary subsuming clause
  File * output;                // output file

  Internal * internal;          // proxy to 'this' in macros (redundant)
  External * external;		// proxy to 'external' buddy in 'Solver'

  /*----------------------------------------------------------------------*/

  Internal ();
  ~Internal ();

  // Internal delegates and helpers for corresponding functions in
  // 'External' and 'Solver'.  The 'init' function initializes variables up
  // to and including the requested variable index.
  //
  void init_queue (int new_max_var);
  void init (int new_max_var);
  void add_original_lit (int elit);

  // Enlarge tables.
  //
  void enlarge_vals (int new_vsize);
  void enlarge (int new_max_var);

  // A variable is 'active' if it is not eliminated nor fixed.
  //
  bool active (int lit) { return flags(lit).active (); }

  int active_variables () const {
    int res = max_var;
    res -= stats.now.fixed;
    res -= stats.now.eliminated;
    res -= stats.now.substituted;
    assert (res >= 0);
    return res;
  }

  // Regularly reports what is going on in 'report.cpp'.
  //
  void report (char type, int verbose_level = 0);

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
  int & propfixed (int lit)   { return ptab[vlit (lit)]; }

  const Flags & flags (int lit) const { return ftab[vidx (lit)]; }

  const bool occs () const { return otab != 0; }
  const bool watches () const { return wtab != 0; }

  Bins & bins (int lit) { assert (big); return big[vlit (lit)]; }
  Occs & occs (int lit) { assert (otab); return otab[vlit (lit)]; }
  long & noccs (int lit) { assert (ntab); return ntab[vlit (lit)]; }
  long & noccs2 (int lit) { assert (ntab2); return ntab2[vidx (lit)]; }
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
    ws.push_back (Watch (blit, c));
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
  Clause * new_clause (bool red, int glue = 0);
  size_t shrink_clause_size (Clause *, int new_size);
  void deallocate_clause (Clause *);
  void delete_clause (Clause *);
  void mark_garbage (Clause *);
  bool tautological_clause ();
  void add_new_original_clause ();
  Clause * new_learned_redundant_clause (int glue);
  Clause * new_hyper_binary_resolved_clause (bool red, int glue);
  Clause * new_clause_as (const Clause * orig);
  Clause * new_resolved_irredundant_clause ();

  // Forward reasoning through propagation in 'propagate.cpp'.
  //
  void search_assign (int lit, Clause *);
  void assign_driving (int lit, Clause * reason);
  void assign_decision (int decision);
  void assign_unit (int lit);
  bool propagate ();

  // Undo and restart in 'backtrack.cpp'.
  //
  void search_unassign (int lit);
  void backtrack (int target_level = 0);

  // Minimized learned clauses in 'minimize.cpp'.
  //
  bool minimize_literal (int lit, int depth = 0);
  void minimize_clause ();

  // Learning from conflicts in 'analyze.cc'.
  //
  void learn_empty_clause ();
  void learn_unit_clause (int lit);
  void bump_variable (int lit);
  void bump_variables ();
  void bump_clause (Clause *);
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

  // Resetting the saved phased.
  bool rephasing ();
  void rephase ();

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
  void update_clause_useful_probability (Clause*, bool used);
  void mark_useless_redundant_clauses_as_garbage ();
  void unprotect_reasons ();
  void reduce ();

  // Garbage collection called from 'reduce' and during preprocessing.
  //
  int clause_contains_fixed_literal (Clause *);
  void remove_falsified_literals (Clause *);
  void mark_satisfied_clauses_as_garbage ();
  void copy_clause (Clause *);
  void flush_watches (int lit, Watches &);
  size_t flush_occs (int lit);
  void flush_all_occs_and_watches ();
  void copy_non_garbage_clauses ();
  void delete_garbage_clauses ();
  void check_clause_stats ();
  void check_var_stats ();
  bool arenaing ();
  void garbage_collection ();

  // Set-up occurrence list counters and containers.
  //
  void init_doms ();
  void init_occs ();
  void init_bins ();
  void init_noccs ();
  void init_noccs2 ();
  void init_watches ();
  void reset_doms ();
  void reset_occs ();
  void reset_bins ();
  void reset_noccs ();
  void reset_noccs2 ();
  void reset_watches ();

  // Operators on watches.
  //
  void sort_watches ();
  void connect_watches (bool irredundant_only = false);
  void connect_irredundant_watches ();
  void disconnect_watches ();

  // Regular forward subsumption checking.
  //
  bool subsuming ();
  void strengthen_clause (Clause *, int);
  void subsume_clause (Clause * subsuming, Clause * subsumed);
  int subsume_check (Clause * subsuming, Clause * subsumed);
  int try_to_subsume_clause (Clause *, vector<Clause*> & shrunken);
  void subsume_round ();
  void reset_added ();
  void subsume ();

  // Strengthening through vivification and asymmetric tautology elimination.
  //
  void flush_vivification_schedule (vector<Clause*> &);
  void vivify ();

  // Compactification (shrinking internal variable tables).
  //
  bool compactifying ();
  void compact ();

  // Transitive reduction of binary implication graph.
  //
  void transred ();

  // We monitor the maximum glue and maximum size of clauses during 'reduce'
  // and thus can predict if a redundant extended clause is likely to be
  // kept in the next 'reduce' phase.  These clauses are target of
  // subsumption checks, in addition to irredundant and non-extended
  // clauses.  Their variables are marked as being 'added'.
  //
  bool likely_to_be_kept_clause (Clause * c) {
    if (!c->redundant) return true;
    return c->size <= lim.keptsize && c->glue <= lim.keptglue;
  }

  double clause_useful (Clause * c) { return ws/c->size + wg/c->glue; }

  // We mark variables in added or shrunken clauses as being 'added' if the
  // clause is likely to be kept in the next 'reduce' phase (see last
  // function above).  This gives a persistent (across consecutive
  // interleaved search and inprocessing phases) of variables which have to
  // be reconsidered in subsumption checks, e.g., only clauses with 'added'
  // variables are checked to be forward subsumed.
  //
  void mark_added (int lit) {
    Flags & f = flags (lit);
    if (f.added) return;
    LOG ("marking %d as added", abs (lit));
    f.added = true;
    stats.added++;
  }
  void mark_added (Clause *);

  // If irredundant clauses are removed or literals in clauses are removed,
  // then variables in these clauses should be reconsidered to be eliminated
  // through bounded variable elimination.  In contrast to 'removed' the
  // 'added' flag is restricted to 'irredundant' clauses only.
  //
  void mark_removed (int lit) {
    Flags & f = flags (lit);
    if (f.removed) return;
    LOG ("marking %d as removed", abs (lit));
    f.removed = true;
    stats.removed++;
  }
  void mark_removed (Clause *, int except = 0);

  // Bounded variable elimination.
  //
  bool eliminating ();
  bool resolve_clauses (Clause *, int pivot, Clause *);
  void mark_eliminated_clauses_as_garbage (int pivot);
  void mark_redundant_clauses_with_eliminated_variables_as_garbage ();
  bool elim_resolvents_are_bounded (int pivot, long pos, long neg);
  void elim_update_removed (Clause *, int except = 0);
  void elim_update_added (Clause *);
  void elim_add_resolvents (int pivot);
  void try_to_eliminate_variable (int pivot);
  void reset_removed ();
  bool elim_round ();
  void elim ();

  // Failed literal probing.
  //
  bool probing ();
  void failed_literal (int lit);
  void probe_assign_unit (int lit);
  void probe_assign_decision (int lit);
  void probe_assign (int lit, int parent);
  void probe_unassign (int lit);
  void mark_duplicated_binary_clauses_as_garbage ();
  int probe_dominator (int a, int b);
  int hyper_binary_resolve (Clause*);
  void packtrack (int probe);
  void probagate2 ();
  bool probagate ();
  void generate_probes ();
  int next_probe ();
  void probe_core ();
  void probe ();

  // Detect strongly connected components in the binary implication graph
  // (BIG) and perform equivalent literal substitution (ELS).
  //
  bool decompose_round ();
  void decompose ();

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

#ifndef QUIET
  // Built in profiling in 'profile.cpp'.
  //
  void start_profiling (Profile * p, double);
  void stop_profiling (Profile * p, double);

  void start_profiling (Profile * p) { start_profiling (p, process_time ()); }
  void stop_profiling (Profile * p) { stop_profiling (p, process_time ()); }

  void update_all_timers (double now);
  void print_profile (double now);
#endif

  // Get the value of an internal literal: -1=false, 0=unassigned, 1=true.
  // We use a redundant table for both negative and positive literals.  This
  // allows a branch-less check for the value of literal and is considered
  // substantially faster than negating the result if the argument is
  // negative.  We also avoid taking the absolute value.
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

  int externalize (int lit) {
    assert (lit != INT_MIN);
    const int idx = abs (lit);
    assert (idx), assert (idx <= max_var);
    int res = i2e[idx];
    if (lit < 0) res = -res;
    return res;
  }

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

// Has to be put here, e.g., not into 'elim.hpp', since we need the
// definition of 'Internal::noccs2' which in turn requires that the
// 'Internal' member 'esched' is defined.

inline bool more_noccs2::operator () (int a, int b) {
  size_t s = internal->noccs2 (a), t = internal->noccs2 (b);
  if (s > t) return true;
  if (s < t) return false;
  assert (a > 0), assert (b > 0);
  return a > b;
}

/*------------------------------------------------------------------------*/

// Same here, e.g., we put this inlined function here such that we can
// include the 'proof.hpp' header above without having 'Internal' yet.

inline int Proof::externalize (int lit) {
  int res = internal->externalize (lit);
  assert (res);
  return res;
}

};

#endif
