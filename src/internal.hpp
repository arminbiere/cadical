#ifndef _internal_hpp_INCLUDED
#define _internal_hpp_INCLUDED

/*------------------------------------------------------------------------*/

// Wrapped build specific headers which should go first.

#include "inttypes.hpp"

/*------------------------------------------------------------------------*/

// Common 'C' headers.

#include <cassert>
#include <climits>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cctype>
#include <csignal>

// Less common 'C' header.

extern "C" {
#include <unistd.h>
}

/*------------------------------------------------------------------------*/

// Common 'C++' headers.

#include <algorithm>
#include <queue>
#include <string>
#include <vector>

/*------------------------------------------------------------------------*/

// All internal headers are included here.  This gives a nice overview on
// what is needed altogether. The 'Internal' class needs almost all the
// headers anyhow (since the idea is to avoid pointer references as much as
// possible).  Most implementation files need to see the definition of the
// 'Internal' too.  Thus there is no real advantage in trying to reduce the
// number of header files included here.  The other benefit of having all
// header files here is that '.cpp' files then only need to include this.

#include "arena.hpp"
#include "averages.hpp"
#include "bins.hpp"
#include "block.hpp"
#include "cadical.hpp"
#include "checker.hpp"
#include "clause.hpp"
#include "config.hpp"
#include "contract.hpp"
#include "cover.hpp"
#include "elim.hpp"
#include "ema.hpp"
#include "external.hpp"
#include "file.hpp"
#include "flags.hpp"
#include "format.hpp"
#include "heap.hpp"
#include "instantiate.hpp"
#include "internal.hpp"
#include "level.hpp"
#include "limit.hpp"
#include "logging.hpp"
#include "message.hpp"
#include "observer.hpp"
#include "occs.hpp"
#include "options.hpp"
#include "parse.hpp"
#include "phases.hpp"
#include "profile.hpp"
#include "proof.hpp"
#include "queue.hpp"
#include "radix.hpp"
#include "random.hpp"
#include "range.hpp"
#include "reap.hpp"
#include "reluctant.hpp"
#include "resources.hpp"
#include "score.hpp"
#include "stats.hpp"
#include "terminal.hpp"
#include "tracer.hpp"
#include "util.hpp"
#include "var.hpp"
#include "version.hpp"
#include "vivify.hpp"
#include "watch.hpp"

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

using namespace std;

struct Coveror;
struct External;
struct Walker;

struct CubesWithStatus {
  int status;
  std::vector<std::vector<int>> cubes;
};

/*------------------------------------------------------------------------*/

struct Internal {

  /*----------------------------------------------------------------------*/

  // The actual internal state of the solver is set and maintained in this
  // section.  This is currently only used for debugging and testing.

  enum Mode {
    BLOCK    = (1<<0),
    CONDITION= (1<<1),
    COVER    = (1<<2),
    DECOMP   = (1<<3),
    DEDUP    = (1<<4),
    ELIM     = (1<<5),
    LUCKY    = (1<<6),
    PROBE    = (1<<7),
    SEARCH   = (1<<8),
    SIMPLIFY = (1<<9),
    SUBSUME  = (1<<10),
    TERNARY  = (1<<11),
    TRANSRED = (1<<12),
    VIVIFY   = (1<<13),
    WALK     = (1<<14),
  };

  bool in_mode (Mode m) const { return (mode & m) != 0; }
  void set_mode (Mode m) { assert (!(mode & m)); mode |= m; }
  void reset_mode (Mode m) { assert (mode & m); mode &= ~m; }
  void require_mode (Mode m) const { assert (mode & m), (void) m; }

  /*----------------------------------------------------------------------*/

  int mode;                     // current internal state
  bool unsat;                   // empty clause found or learned
  bool iterating;               // report learned unit ('i' line)
  bool localsearching;          // true during local search
  bool lookingahead;            // true during look ahead
  bool preprocessing;           // true during preprocessing
  bool protected_reasons;       // referenced reasons are protected
  bool force_saved_phase;       // force saved phase in decision
  bool searching_lucky_phases;  // during 'lucky_phases'
  bool stable;                  // true during stabilization phase
  bool reported;                // reported in this solving call
  char rephased;                // last type of resetting phases
  Reluctant reluctant;          // restart counter in stable mode
  size_t vsize;                 // actually allocated variable data size
  int max_var;                  // internal maximum variable index
  int level;                    // decision level ('control.size () - 1')
  Phases phases;                // saved, target and best phases
  signed char * vals;           // assignment [-max_var,max_var]
  vector<signed char> marks;    // signed marks [1,max_var]
  vector<unsigned> frozentab;   // frozen counters [1,max_var]
  vector<int> i2e;              // maps internal 'idx' to external 'lit'
  Queue queue;                  // variable move to front decision queue
  Links links;                  // table of links for decision queue
  double score_inc;             // current score increment
  ScoreSchedule scores;         // score based decision priority queue
  vector<double> stab;          // table of variable scores [1,max_var]
  vector<Var> vtab;             // variable table [1,max_var]
  vector<int> parents;          // parent literals during probing
  vector<Flags> ftab;           // variable and literal flags
  vector<int64_t> btab;         // enqueue time stamps for queue
  vector<int64_t> gtab;         // time stamp table to recompute glue
  vector<Occs> otab;            // table of occurrences for all literals
  vector<int> ptab;             // table for caching probing attempts
  vector<int64_t> ntab;         // number of one-sided occurrences table
  vector<Bins> big;             // binary implication graph
  vector<Watches> wtab;         // table of watches for all literals
  Clause * conflict;            // set in 'propagation', reset in 'analyze'
  Clause * ignore;              // ignored during 'vivify_propagate'
  size_t propagated;            // next trail position to propagate
  size_t propagated2;           // next binary trail position to propagate
  size_t best_assigned;         // best maximum assigned ever
  size_t target_assigned;       // maximum assigned without conflict
  size_t no_conflict_until;     // largest trail prefix without conflict
  vector<int> trail;            // currently assigned literals
  vector<int> clause;           // simplified in parsing & learning
  vector<int> assumptions;      // assumed literals
  vector<int> constraint;       // literals of the constraint
  bool unsat_constraint;        // constraint used for unsatisfiability?
  bool marked_failed;           // are the failed assumptions marked?
  vector<int> original;         // original added literals
  vector<int> levels;           // decision levels in learned clause
  vector<int> analyzed;         // analyzed literals in 'analyze'
  vector<int> minimized;        // removable or poison in 'minimize'
  vector<int> shrinkable;       // removable or poison in 'shrink'
  Reap reap;                    // radix heap for shrink

  vector<int> probes;           // remaining scheduled probes
  vector<Level> control;        // 'level + 1 == control.size ()'
  vector<Clause*> clauses;      // ordered collection of all clauses
  Averages averages;            // glue, size, jump moving averages
  Limit lim;                    // limits for various phases
  Last last;                    // statistics at last occurrence
  Inc inc;                      // increments on limits
  Proof * proof;                // clausal proof observers if non zero
  Checker * checker;            // online proof checker observing proof
  Tracer * tracer;              // proof to file tracer observing proof
  Options opts;                 // run-time options
  Stats stats;                  // statistics
#ifndef QUIET
  Profiles profiles;            // time profiles for various functions
  bool force_phase_messages;    // force 'phase (...)' messages
#endif
  Arena arena;                  // memory arena for moving garbage collector
  Format error_message;         // provide persistent error message
  string prefix;                // verbose messages prefix

  Internal * internal;          // proxy to 'this' in macros
  External * external;          // proxy to 'external' buddy in 'Solver'

  /*----------------------------------------------------------------------*/

  // Asynchronous termination flag written by 'terminate' and read by
  // 'terminated_asynchronously' (the latter at the end of this header).
  //
  volatile bool termination_forced;

  /*----------------------------------------------------------------------*/

  const Range vars;             // Provides safe variable iteration.
  const Sange lits;             // Provides safe literal iteration.

  /*----------------------------------------------------------------------*/

  Internal ();
  ~Internal ();

  /*----------------------------------------------------------------------*/

  // Internal delegates and helpers for corresponding functions in
  // 'External' and 'Solver'.  The 'init_vars' function initializes
  // variables up to and including the requested variable index.
  //
  void init_vars (int new_max_var);

  void init_enqueue (int idx);
  void init_queue (int old_max_var, int new_max_var);

  void init_scores (int old_max_var, int new_max_var);

  void add_original_lit (int lit);

  // Enlarge tables.
  //
  void enlarge_vals (size_t new_vsize);
  void enlarge (int new_max_var);

  // A variable is 'active' if it is not eliminated nor fixed.
  //
  bool active (int lit) { return flags(lit).active (); }

  int active () const {
    int res = stats.active;
#ifndef NDEBUG
    int tmp = max_var;
    tmp -= stats.unused;
    tmp -= stats.now.fixed;
    tmp -= stats.now.eliminated;
    tmp -= stats.now.substituted;
    tmp -= stats.now.pure;
    assert (tmp >= 0);
    assert (tmp == res);
#endif
    return res;
  }

  void reactivate (int lit);    // During 'restore'.

  // Currently remaining active redundant and irredundant clauses.

  int64_t redundant () const { return stats.current.redundant; }

  int64_t irredundant () const { return stats.current.irredundant; }

  double clause_variable_ratio () const {
    return relative (irredundant (), active ());
  }

  // Scale values relative to clause variable ratio.
  //
  double scale (double v) const;

  // Unsigned literals (abs) with checks.
  //
  int vidx (int lit) const {
    int idx;
    assert (lit);
    assert (lit != INT_MIN);
    idx = abs (lit);
    assert (idx <= max_var);
    return idx;
  }

  // Unsigned version with LSB denoting sign.  This is used in indexing arrays
  // by literals.  The idea is to keep the elements in such an array for both
  // the positive and negated version of a literal close together.
  //
  unsigned vlit (int lit) { return (lit < 0) + 2u * (unsigned) vidx (lit); }

  int u2i (unsigned u) {
    assert (u > 1);
    int res = u/2;
    assert (res <= max_var);
    if (u & 1) res = -res;
    return res;
  }

  // Helper functions to access variable and literal data.
  //
  Var & var (int lit)        { return vtab[vidx (lit)]; }
  Link & link (int lit)      { return links[vidx (lit)]; }
  Flags & flags (int lit)    { return ftab[vidx (lit)]; }
  int64_t & bumped (int lit) { return btab[vidx (lit)]; }
  int & propfixed (int lit)  { return ptab[vlit (lit)]; }
  double & score (int lit)   { return stab[vidx (lit)]; }

  const Flags &
  flags (int lit) const       { return ftab[vidx (lit)]; }

  bool occurring () const     { return !otab.empty (); }
  bool watching () const      { return !wtab.empty (); }

  Bins & bins (int lit)       { return big[vlit (lit)]; }
  Occs & occs (int lit)       { return otab[vlit (lit)]; }
  int64_t & noccs (int lit)   { return ntab[vlit (lit)]; }
  Watches & watches (int lit) { return wtab[vlit (lit)]; }

  // Variable bumping through exponential VSIDS (EVSIDS) as in MiniSAT.
  //
  bool use_scores () const { return opts.score && stable; }
  void bump_variable_score (int lit);
  void bump_variable_score_inc ();
  void rescale_variable_scores ();

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
    assert (marked (lit) > 0);
    assert (marked (-lit) < 0);
  }
  void unmark (int lit) {
    marks [ vidx (lit) ] = 0;
    assert (!marked (lit));
  }

  // Use only bits 6 and 7 to store the sign or zero.  The remaining
  // bits can be use as additional flags.
  //
  signed char marked67 (int lit) const {
    signed char res = marks [ vidx (lit) ] >> 6;
    if (lit < 0) res = -res;
    return res;
  }
  void mark67 (int lit) {
    signed char & m = marks[vidx (lit)];
    const signed char mask = 0x3f;
#ifndef NDEBUG
    const signed char bits = m & mask;
#endif
    m = (m & mask) | (sign (lit) << 6);
    assert (marked (lit) > 0);
    assert (marked (-lit) < 0);
    assert ((m & mask) == bits);
    assert (marked67 (lit) > 0);
    assert (marked67 (-lit) < 0);
  }
  void unmark67 (int lit) {
    signed char & m = marks[vidx (lit)];
    const signed char mask = 0x3f;
#ifndef NDEBUG
    const signed bits = m & mask;
#endif
    m &= mask;
    assert ((m & mask) == bits);
  }

  void unmark (vector<int> & lits) {
    for (const auto & lit : lits)
      unmark (lit);
  }

  // The other 6 bits of the 'marks' bytes can be used as additional
  // (unsigned) marking bits.  Currently we only use the least significant
  // bit in 'condition' to mark variables in the conditional part.
  //
  bool getbit (int lit, int bit) const {
    assert (0 <= bit), assert (bit < 6);
    return marks[vidx (lit)] & (1<<bit);
  }
  void setbit (int lit, int bit) {
    assert (0 <= bit), assert (bit < 6);
    assert (!getbit (lit, bit));
    marks[vidx (lit)] |= (1<<bit);
    assert (getbit (lit, bit));
  }
  void unsetbit (int lit, int bit) {
    assert (0 <= bit), assert (bit < 6);
    assert (getbit (lit, bit));
    marks[vidx (lit)] &= ~(1<<bit);
    assert (!getbit (lit, bit));
  }

  // Marking individual literals.
  //
  bool marked2 (int lit) const {
    unsigned res = marks [ vidx (lit) ];
    assert (res <= 3);
    unsigned bit = bign (lit);
    return (res & bit) != 0;
  }
  void mark2 (int lit) {
    marks[vidx (lit)] |= bign (lit);
    assert (marked2 (lit));
  }

  // Marking and unmarking of all literals in a clause.
  //
  void mark_clause ();          // mark 'this->clause'
  void mark (Clause *);
  void mark2 (Clause *);
  void unmark_clause ();        // unmark 'this->clause'
  void unmark (Clause *);

  // Watch literal 'lit' in clause with blocking literal 'blit'.
  // Inlined here, since it occurs in the tight inner loop of 'propagate'.
  //
  inline void watch_literal (int lit, int blit, Clause * c) {
    assert (lit != blit);
    Watches & ws = watches (lit);
    ws.push_back (Watch (blit, c));
    LOG (c, "watch %d blit %d in", lit, blit);
  }

  // Add two watches to a clause.  This is used initially during allocation
  // of a clause and during connecting back all watches after preprocessing.
  //
  inline void watch_clause (Clause * c) {
    const int l0 = c->literals[0];
    const int l1 = c->literals[1];
    watch_literal (l0, l1, c);
    watch_literal (l1, l0, c);
  }

  inline void unwatch_clause (Clause * c) {
    const int l0 = c->literals[0];
    const int l1 = c->literals[1];
    remove_watch (watches (l0), c);
    remove_watch (watches (l1), c);
  }

  // Update queue to point to last potentially still unassigned variable.
  // All variables after 'queue.unassigned' in bump order are assumed to be
  // assigned.  Then update the 'queue.bumped' field and log it.  This is
  // inlined here since it occurs in several inner loops.
  //
  inline void update_queue_unassigned (int idx) {
    assert (0 < idx);
    assert (idx <= max_var);
    queue.unassigned = idx;
    queue.bumped = btab[idx];
    LOG ("queue unassigned now %d bumped %" PRId64 "", idx, btab[idx]);
  }

  void bump_queue (int idx);

  // Mark (active) variables as eliminated, substituted, pure or fixed,
  // which turns them into inactive variables.
  //
  void mark_eliminated (int);
  void mark_substituted (int);
  void mark_active (int);
  void mark_fixed (int);
  void mark_pure (int);

  // Managing clauses in 'clause.cpp'.  Without explicit 'Clause' argument
  // these functions work on the global temporary 'clause'.
  //
  Clause * new_clause (bool red, int glue = 0);
  void promote_clause (Clause *, int new_glue);
  size_t shrink_clause (Clause *, int new_size);
  void minimize_sort_clause();
  void shrink_and_minimize_clause ();
  void reset_shrinkable();
  void mark_shrinkable_as_removable(int, std::vector<int>::size_type);
  int shrink_literal(int, int, unsigned);
  unsigned shrunken_block_uip(int, int, std::vector<int>::reverse_iterator &,
                              std::vector<int>::reverse_iterator &,
                              std::vector<int>::size_type, const int);
  void shrunken_block_no_uip(const std::vector<int>::reverse_iterator&, const std::vector<int>::reverse_iterator&, unsigned&, const int);
  void push_literals_of_block(const std::vector<int>::reverse_iterator&, const std::vector<int>::reverse_iterator&, int, unsigned);
  unsigned shrink_next(unsigned&, unsigned&);
  std::vector<int>::reverse_iterator minimize_and_shrink_block(std::vector<int>::reverse_iterator&, unsigned int&, unsigned int&, const int);
  unsigned shrink_block(std::vector<int>::reverse_iterator&, std::vector<int>::reverse_iterator&, int, unsigned&, unsigned&, const int, unsigned);
  unsigned shrink_along_reason(int, int, bool, bool&, unsigned);

  void deallocate_clause(Clause *);
  void delete_clause (Clause *);
  void mark_garbage (Clause *);
  void assign_original_unit (int);
  void add_new_original_clause ();
  Clause * new_learned_redundant_clause (int glue);
  Clause * new_hyper_binary_resolved_clause (bool red, int glue);
  Clause * new_clause_as (const Clause * orig);
  Clause * new_resolved_irredundant_clause ();

  // Forward reasoning through propagation in 'propagate.cpp'.
  //
  int assignment_level (int lit, Clause*);
  void search_assign (int lit, Clause *);
  void search_assign_driving (int lit, Clause * reason);
  void search_assume_decision (int decision);
  void assign_unit (int lit);
  bool propagate ();

  // Undo and restart in 'backtrack.cpp'.
  //
  void unassign (int lit);
  void update_target_and_best ();
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
  int recompute_glue (Clause *);
  void bump_clause (Clause *);
  void clear_analyzed_literals ();
  void clear_analyzed_levels ();
  void clear_minimized_literals ();
  bool bump_also_reason_literal (int lit);
  void bump_also_reason_literals (int lit, int limit);
  void bump_also_all_reason_literals ();
  void analyze_literal (int lit, int & open);
  void analyze_reason (int lit, Clause *, int & open);
  Clause * new_driving_clause (const int glue, int & jump);
  int find_conflict_level (int & forced);
  int determine_actual_backtrack_level (int jump);
  void analyze ();
  void iterate ();       // report learned unit clause

  // Use last learned clause to subsume some more.
  //
  void eagerly_subsume_recently_learned_clauses (Clause *);

  // Restarting policy in 'restart.cc'.
  //
  bool stabilizing ();
  bool restarting ();
  int reuse_trail ();
  void restart ();

  // Functions to set and reset certain 'phases'.
  //
  void clear_phases (vector<signed char> &);  // reset argument to zero
  void copy_phases (vector<signed char> &);   // copy 'saved' to argument

  // Resetting the saved phased in 'rephase.cpp'.
  //
  bool rephasing ();
  char rephase_best ();
  char rephase_flipping ();
  char rephase_inverted ();
  char rephase_original ();
  char rephase_random ();
  char rephase_walk ();
  void shuffle_scores ();
  void shuffle_queue ();
  void rephase ();

  // Lucky feasible case checking.
  //
  int unlucky (int res);
  int trivially_false_satisfiable ();
  int trivially_true_satisfiable ();
  int forward_false_satisfiable ();
  int forward_true_satisfiable ();
  int backward_false_satisfiable ();
  int backward_true_satisfiable ();
  int positive_horn_satisfiable ();
  int negative_horn_satisfiable ();

  // Asynchronous terminating check.
  //
  bool terminated_asynchronously (int factor = 1);

  bool search_limits_hit ();

  void terminate () {
    LOG ("forcing asynchronous termination");
    termination_forced = true;
  }

  // Reducing means determining useless clauses with 'reduce' in
  // 'reduce.cpp' as well as root level satisfied clause and then removing
  // those which are not used as reason anymore with garbage collection.
  //
  bool flushing ();
  bool reducing ();
  void protect_reasons ();
  void mark_clauses_to_be_flushed ();
  void mark_useless_redundant_clauses_as_garbage ();
  bool propagate_out_of_order_units ();
  void unprotect_reasons ();
  void reduce ();

  // Garbage collection in 'collect.cpp' called from 'reduce' and during
  // inprocessing and preprocessing.
  //
  int clause_contains_fixed_literal (Clause *);
  void remove_falsified_literals (Clause *);
  void mark_satisfied_clauses_as_garbage ();
  void copy_clause (Clause *);
  void flush_watches (int lit, Watches &);
  size_t flush_occs (int lit);
  void flush_all_occs_and_watches ();
  void update_reason_references ();
  void copy_non_garbage_clauses ();
  void delete_garbage_clauses ();
  void check_clause_stats ();
  void check_var_stats ();
  bool arenaing ();
  void garbage_collection ();

  // Set-up occurrence list counters and containers.
  //
  void init_occs ();
  void init_bins ();
  void init_noccs ();
  void reset_occs ();
  void reset_bins ();
  void reset_noccs ();

  // Operators on watches.
  //
  void init_watches ();
  void connect_watches (bool irredundant_only = false);
  void sort_watches ();
  void clear_watches ();
  void reset_watches ();

  // Regular forward subsumption checking in 'subsume.cpp'.
  //
  bool subsuming ();
  void strengthen_clause (Clause *, int);
  void subsume_clause (Clause * subsuming, Clause * subsumed);
  int subsume_check (Clause * subsuming, Clause * subsumed);
  int try_to_subsume_clause (Clause *, vector<Clause*> & shrunken);
  void reset_subsume_bits ();
  bool subsume_round ();
  void subsume (bool update_limits = true);

  // Covered clause elimination of large clauses.
  //
  void covered_literal_addition (int lit, Coveror &);
  void asymmetric_literal_addition (int lit, Coveror &);
  void cover_push_extension (int lit, Coveror &);
  bool cover_propagate_asymmetric (int lit, Clause * ignore, Coveror &);
  bool cover_propagate_covered (int lit, Coveror &);
  bool cover_clause (Clause * c, Coveror &);
  int64_t cover_round ();
  bool cover ();

  // Strengthening through vivification in 'vivify.cpp'.
  //
  void flush_vivification_schedule (Vivifier &);
  bool consider_to_vivify_clause (Clause * candidate, bool redundant_mode);
  void vivify_analyze_redundant (Vivifier &, Clause * start, bool &);
  bool vivify_all_decisions (Clause * candidate, int subsume);
  void vivify_post_process_analysis (Clause * candidate, int subsume);
  void vivify_strengthen (Clause * candidate);
  void vivify_assign (int lit, Clause *);
  void vivify_assume (int lit);
  bool vivify_propagate ();
  void vivify_clause (Vivifier &, Clause * candidate);
  void vivify_round (bool redundant_mode, int64_t delta);
  void vivify ();

  // Compacting (shrinking internal variable tables) in 'compact.cpp'
  //
  bool compacting ();
  void compact ();

  // Transitive reduction of binary implication graph in 'transred.cpp'
  //
  void transred ();

  // We monitor the maximum size and glue of clauses during 'reduce' and
  // thus can predict if a redundant extended clause is likely to be kept in
  // the next 'reduce' phase.  These clauses are target of subsumption and
  // vivification checks, in addition to irredundant clauses.  Their
  // variables are also marked as being 'added'.
  //
  bool likely_to_be_kept_clause (Clause * c) {
    if (!c->redundant) return true;
    if (c->keep) return true;
    if (c->glue > lim.keptglue) return false;
    if (c->size > lim.keptsize) return false;
    return true;
  }

  // We mark variables in added or shrunken clauses as 'subsume' candidates
  // if the clause is likely to be kept in the next 'reduce' phase (see last
  // function above).  This gives a persistent (across consecutive
  // interleaved search and inprocessing phases) set of variables which have
  // to be reconsidered in subsumption checks, i.e., only clauses with
  // 'subsume' marked variables are checked to be forward subsumed.
  // A similar technique is used to reduce the effort in hyper ternary
  // resolution to focus on variables in new ternary clauses.
  //
  void mark_subsume (int lit) {
    Flags & f = flags (lit);
    if (f.subsume) return;
    LOG ("marking %d as subsuming literal candidate", abs (lit));
    stats.mark.subsume++;
    f.subsume = true;
  }
  void mark_ternary (int lit) {
    Flags & f = flags (lit);
    if (f.ternary) return;
    LOG ("marking %d as ternary resolution literal candidate", abs (lit));
    stats.mark.ternary++;
    f.ternary = true;
  }
  void mark_added (int lit, int size, bool redundant);
  void mark_added (Clause *);

  bool marked_subsume(int lit) const { return flags(lit).subsume; }

    // If irredundant clauses are removed or literals in clauses are removed,
    // then variables in such clauses should be reconsidered to be eliminated
    // through bounded variable elimination.  In contrast to 'subsume' the
    // 'elim' flag is restricted to 'irredundant' clauses only. For blocked
    // clause elimination it is better to have a more precise signed version,
    // which allows to independently mark positive and negative literals.
    //
    void mark_elim(int lit) {
      Flags &f = flags(lit);
      if (f.elim)
        return;
      LOG("marking %d as elimination literal candidate", lit);
      stats.mark.elim++;
      f.elim = true;
    }
    void mark_block(int lit) {
      Flags &f = flags(lit);
      const unsigned bit = bign(lit);
      if (f.block & bit)
        return;
      LOG("marking %d as blocking literal candidate", lit);
      stats.mark.block++;
      f.block |= bit;
    }
    void mark_removed(int lit) {
      mark_elim(lit);
      mark_block(-lit);
    }
    void mark_removed(Clause *, int except = 0);

    // The following two functions are only used for testing & debugging.

    bool marked_block(int lit) const {
      const Flags &f = flags(lit);
      const unsigned bit = bign(lit);
      return (f.block & bit) != 0;
    }
    void unmark_block(int lit) {
      Flags &f = flags(lit);
      const unsigned bit = bign(lit);
      f.block &= ~bit;
    }

    // During scheduling literals for blocked clause elimination we skip those
    // literals which occur negated in a too large clause.
    //
    void mark_skip(int lit) {
      Flags &f = flags(lit);
      const unsigned bit = bign(lit);
      if (f.skip & bit)
        return;
      LOG("marking %d to be skipped as blocking literal", lit);
      f.skip |= bit;
    }
    bool marked_skip(int lit) {
      const Flags &f = flags(lit);
      const unsigned bit = bign(lit);
      return (f.skip & bit) != 0;
    }

    // Blocked Clause elimination in 'block.cpp'.
    //
    bool is_blocked_clause(Clause * c, int pivot);
    void block_schedule(Blocker &);
    size_t block_candidates(Blocker &, int lit);
    Clause *block_impossible(Blocker &, int lit);
    void block_literal_with_at_least_two_negative_occs(Blocker &, int lit);
    void block_literal_with_one_negative_occ(Blocker &, int lit);
    void block_pure_literal(Blocker &, int lit);
    void block_reschedule_clause(Blocker &, int lit, Clause *);
    void block_reschedule(Blocker &, int lit);
    void block_literal(Blocker &, int lit);
    bool block();

    // Find gates in 'gates.cpp' for bounded variable substitution.
    //
    int second_literal_in_binary_clause(Eliminator &, Clause *, int first);
    void mark_binary_literals(Eliminator &, int pivot);
    void find_and_gate(Eliminator &, int pivot);
    void find_equivalence(Eliminator &, int pivot);

    bool get_ternary_clause(Clause *, int &, int &, int &);
    bool match_ternary_clause(Clause *, int, int, int);
    Clause *find_ternary_clause(int, int, int);

    bool get_clause(Clause *, vector<int> &);
    bool is_clause(Clause *, const vector<int> &);
    Clause *find_clause(const vector<int> &);
    void find_xor_gate(Eliminator &, int pivot);

    void find_if_then_else(Eliminator &, int pivot);

    void find_gate_clauses(Eliminator &, int pivot);
    void unmark_gate_clauses(Eliminator &);

    // Bounded variable elimination in 'elim.cpp'.
    //
    bool eliminating();
    double compute_elim_score(unsigned lit);
    void mark_redundant_clauses_with_eliminated_variables_as_garbage();
    void unmark_binary_literals(Eliminator &);
    bool resolve_clauses(Eliminator &, Clause *, int pivot, Clause *, bool);
    void mark_eliminated_clauses_as_garbage(Eliminator &, int pivot);
    bool elim_resolvents_are_bounded(Eliminator &, int pivot);
    void elim_update_removed_lit(Eliminator &, int lit);
    void elim_update_removed_clause(Eliminator &, Clause *, int except = 0);
    void elim_update_added_clause(Eliminator &, Clause *);
    void elim_add_resolvents(Eliminator &, int pivot);
    void elim_backward_clause(Eliminator &, Clause *);
    void elim_backward_clauses(Eliminator &);
    void elim_propagate(Eliminator &, int unit);
    void elim_on_the_fly_self_subsumption(Eliminator &, Clause *, int);
    void try_to_eliminate_variable(Eliminator &, int pivot);
    void increase_elimination_bound();
    int elim_round(bool &completed);
    void elim(bool update_limits = true);

    void inst_assign(int lit);
    bool inst_propagate();
    void collect_instantiation_candidates(Instantiator &);
    bool instantiate_candidate(int lit, Clause *);
    void instantiate(Instantiator &);

    // Hyper ternary resolution.
    //
    bool ternary_find_binary_clause(int, int);
    bool ternary_find_ternary_clause(int, int, int);
    Clause *new_hyper_ternary_resolved_clause(bool red);
    bool hyper_ternary_resolve(Clause *, int, Clause *);
    void ternary_lit(int pivot, int64_t &steps, int64_t &htrs);
    void ternary_idx(int idx, int64_t &steps, int64_t &htrs);
    bool ternary_round(int64_t & steps, int64_t & htrs);
    bool ternary();

    // Probing in 'probe.cpp'.
    //
    bool probing();
    void failed_literal(int lit);
    void probe_assign_unit(int lit);
    void probe_assign_decision(int lit);
    void probe_assign(int lit, int parent);
    void mark_duplicated_binary_clauses_as_garbage();
    int get_parent_reason_literal(int lit);
    void set_parent_reason_literal(int lit, int reason);
    int probe_dominator(int a, int b);
    int hyper_binary_resolve(Clause *);
    void probe_propagate2();
    bool probe_propagate();
    bool is_binary_clause(Clause * c, int &, int &);
    void generate_probes();
    void flush_probes();
    int next_probe();
    bool probe_round();
    void probe(bool update_limits = true);

    // ProbSAT/WalkSAT implementation called initially or from 'rephase'.
    //
    void walk_save_minimum(Walker &);
    Clause *walk_pick_clause(Walker &);
    unsigned walk_break_value(int lit);
    int walk_pick_lit(Walker &, Clause *);
    void walk_flip_lit(Walker &, int lit);
    int walk_round(int64_t limit, bool prev);
    void walk();

    // Detect strongly connected components in the binary implication graph
    // (BIG) and equivalent literal substitution (ELS) in 'decompose.cpp'.
    //
    bool decompose_round();
    void decompose();

    void reset_limits();      // Reset after 'solve' call.

    // Assumption handling.
    //
    void assume(int);         // New assumption literal.
    bool failed(int lit);     // Literal failed assumption?
    void reset_assumptions(); // Reset after 'solve' call.
    void failing();           // Prepare failed assumptions.

    bool assumed(int lit) {   // Marked as assumption.
      Flags &f = flags(lit);
      const unsigned bit = bign(lit);
      return (f.assumed & bit) != 0;
    }

    // Add temporary clause as constraint.
    //
    void constrain(int);      // Add literal to constraint.
    bool failed_constraint(); // Was constraint used to proof unsatisfiablity?
    void reset_constraint();  // Reset after 'solve' call.

    // Forcing decision variables to a certain phase.
    //
    void phase(int lit);
    void unphase(int lit);

    // Globally blocked clause elimination.
    //
    bool is_autarky_literal(int lit) const;
    bool is_conditional_literal(int lit) const;
    void mark_as_conditional_literal(int lit);
    void unmark_as_conditional_literal(int lit);
    //
    bool is_in_candidate_clause(int lit) const;
    void mark_in_candidate_clause(int lit);
    void unmark_in_candidate_clause(int lit);
    //
    void condition_assign(int lit);
    void condition_unassign(int lit);
    //
    bool conditioning();
    long condition_round(long unassigned_literal_propagation_limit);
    void condition(bool update_limits = true);

    // Part on picking the next decision in 'decide.cpp'.
    //
    bool satisfied();
    int next_decision_variable_on_queue();
    int next_decision_variable_with_best_score();
    int next_decision_variable();
    int decide_phase(int idx, bool target);
    int likely_phase(int idx);
    int decide(); // 0=decision, 20=failed

    // Internal functions to enable explicit search limits.
    //
    void limit_terminate(int);
    void limit_decisions(int);     // Force decision limit.
    void limit_conflicts(int);     // Force conflict limit.
    void limit_preprocessing(int); // Enable 'n' preprocessing rounds.
    void limit_local_search(int);  // Enable 'n' local search rounds.

    // External versions can access limits by 'name'.
    //
    static bool is_valid_limit(const char *name);
    bool limit(const char *name, int); // 'true' if 'name' valid

    // Set all the CDCL search limits and increments for scheduling
    // inprocessing, restarts, clause database reductions, etc.
    //
    void init_report_limits();
    void init_preprocessing_limits();
    void init_search_limits();

    // The computed averages are local to the 'stable' and 'unstable' phase.
    // Their main use is to be reported in 'report', except for the 'glue'
    // averages, which are used to schedule (prohibit actually) restarts
    // during 'unstable' phases ('stable' phases use reluctant doubling).
    //
    void init_averages();
    void swap_averages();

    int try_to_satisfy_formula_by_saved_phases();
    void produce_failed_assumptions();

    // Main solve & search functions in 'internal.cpp'.
    //
    // We have three pre-solving techniques.  These consist of preprocessing,
    // local search and searching for lucky phases, which in full solving
    // mode except for the last are usually optional and then followed by
    // the main CDCL search loop with inprocessing.  If only preprocessing
    // is requested from 'External::simplifiy' only preprocessing is called
    // though. This is all orchestrated by the 'solve' function.
    //
    int already_solved();
    int restore_clauses();
    bool preprocess_round(int round);
    int preprocess();
    int local_search_round(int round);
    int local_search();
    int lucky_phases();
    int cdcl_loop_with_inprocessing();
    void reset_solving();
    int solve(bool preprocess_only = false);

    //
    int lookahead();
    CubesWithStatus generate_cubes(int, int);
    int most_occurring_literal();
    int lookahead_probing();
    int lookahead_next_probe();
    void lookahead_flush_probes();
    void lookahead_generate_probes();
    std::vector<int> lookahead_populate_locc();
    int lookahead_locc(const std::vector<int> &);

    bool terminating_asked();

#ifndef QUIET
  // Built in profiling in 'profile.cpp' (see also 'profile.hpp').
  //
  void start_profiling (Profile & p, double);
  void stop_profiling (Profile & p, double);

  double update_profiles ();    // Returns 'time ()'.
  void print_profile ();
#endif

  // Get the value of an internal literal: -1=false, 0=unassigned, 1=true.
  // We use a redundant table for both negative and positive literals.  This
  // allows a branch-less check for the value of literal and is considered
  // substantially faster than negating the result if the argument is
  // negative.  We also avoid taking the absolute value.
  //
  signed char val (int lit) const {
    assert (-max_var <= lit);
    assert (lit);
    assert (lit <= max_var);
    return vals[lit];
  }

  // As 'val' but restricted to the root-level value of a literal.
  // It is not that time critical and also needs to check the decision level
  // of the variable anyhow.
  //
  int fixed (int lit) {
    assert (-max_var <= lit);
    assert (lit);
    assert (lit <= max_var);
    const int idx = vidx (lit);
    int res = vals[idx];
    if (res && vtab[idx].level) res = 0;
    if (lit < 0) res = -res;
    return res;
  }

  // Map back an internal literal to an external.
  //
  int externalize (int lit) {
    assert (lit != INT_MIN);
    const int idx = abs (lit);
    assert (idx);
    assert (idx <= max_var);
    int res = i2e[idx];
    if (lit < 0) res = -res;
    return res;
  }

  // Explicit freezing and melting of variables.
  //
  void freeze (int lit) {
    int idx = vidx (lit);
    unsigned & ref = frozentab[idx];
    if (ref < UINT_MAX) {
      ref++;
      LOG ("variable %d frozen %u times", idx, ref);
    } else LOG ("variable %d remains frozen forever", idx);
  }
  void melt (int lit) {
    int idx = vidx (lit);
    unsigned & ref = frozentab[idx];
    if (ref < UINT_MAX) {
      if (!--ref) {
        LOG ("variable %d completely molten", idx);
      } else
        LOG ("variable %d melted once but remains frozen %u times",
          lit, ref);
    } else LOG ("variable %d remains frozen forever", idx);
  }
  bool frozen (int lit) { return frozentab[vidx (lit)] > 0; }

  // Parsing functions in 'parse.cpp'.
  //
  const char * parse_dimacs (FILE *);
  const char * parse_dimacs (const char *);
  const char * parse_solution (const char *);

  // Enable and disable proof logging and checking.
  //
  void new_proof_on_demand ();
  void close_trace ();          // Stop proof tracing.
  void flush_trace ();          // Flush proof trace file.
  void trace (File *);          // Start write proof file.
  void check ();                // Enable online proof checking.

  // Dump to '<stdout>' as DIMACS for debugging.
  //
  void dump (Clause *);
  void dump ();

  // Export and traverse all irredundant (non-unit) clauses.
  //
  bool traverse_clauses (ClauseIterator &);

  /*----------------------------------------------------------------------*/

  double solve_time ();         // accumulated time spent in 'solve ()'

  double process_time ();       // since solver was initialized
  double real_time ();          // since solver was initialized

  double time () {
    return opts.realtime ? real_time () : process_time ();
  }

  // Regularly reports what is going on in 'report.cpp'.
  //
  void report (char type, int verbose_level = 0);
  void report_solving(int);

  void print_statistics ();
  void print_resource_usage ();

  /*----------------------------------------------------------------------*/

#ifndef QUIET

  void print_prefix ();

  // Non-verbose messages and warnings, i.e., always printed unless 'quiet'
  // is set, which disables messages at run-time, or even 'QUIET' is defined
  // through the configuration option './configure --quiet', which disables
  // such messages completely at compile-time.
  //
  void vmessage (const char *, va_list &);
  void message (const char *, ...)
                CADICAL_ATTRIBUTE_FORMAT (2, 3);
  void message ();                              // empty line

  // Verbose messages with explicit verbose 'level' controlled by
  // 'opts.verbose' (verbose level '0' gives the same as 'message').
  //
  void vverbose (int level, const char * fmt, va_list &);
  void verbose (int level, const char * fmt, ...)
                CADICAL_ATTRIBUTE_FORMAT (3, 4);
  void verbose (int level);

  // This is for printing section headers in the form
  //
  //  c ---- [ <title> ] ---------------------
  //
  // nicely aligned (and of course is ignored if 'quiet' is set).
  //
  void section (const char * title);

  // Print verbose message about phases if 'opts.verbose > 1' (but not if
  // 'quiet' is set).  Note that setting 'log' or '-l' forces all verbose
  // output (and also ignores 'quiet' set to true').  The 'phase' argument
  // is used to print a 'phase' prefix for the message as follows:
  //
  //  c [<phase>] ...
  //
  void phase (const char * phase, const char *, ...)
              CADICAL_ATTRIBUTE_FORMAT (3, 4);

  // Same as the last 'phase' above except that the prefix gets a count:
  //
  //  c [<phase>-<count>] ...
  //
  void phase (const char * phase, int64_t count, const char *, ...)
              CADICAL_ATTRIBUTE_FORMAT (4, 5);
#endif

  // Print error messages which are really always printed (even if 'quiet'
  // is set).  This leads to exit the current process with exit status '1'.
  //
  // TODO add possibility to use a call back instead of calling exit.
  //
  void error_message_end ();
  void verror (const char *, va_list &);
  void error (const char *, ...)
              CADICAL_ATTRIBUTE_FORMAT (2, 3);
  void error_message_start ();

  // Warning messages.
  //
  void warning (const char *, ...)
                CADICAL_ATTRIBUTE_FORMAT (2, 3);
  };

// Fatal internal error which leads to abort.
//
void fatal_message_start ();
void fatal_message_end ();
void fatal (const char *, ...)
            CADICAL_ATTRIBUTE_FORMAT (1, 2);

/*------------------------------------------------------------------------*/

// Has to be put here, i.e., not into 'score.hpp', since we need the
// definition of 'Internal::score' above (after '#include "score.hpp"').

inline bool score_smaller::operator () (unsigned a, unsigned b) {

  // Avoid computing twice 'abs' in 'score ()'.
  //
  assert (1 <= a);
  assert (a <= (unsigned) internal->max_var);
  assert (1 <= b);
  assert (b <= (unsigned) internal->max_var);
  double s = internal->stab[a];
  double t = internal->stab[b];

  if (s < t) return true;
  if (s > t) return false;

  return a > b;
}

/*------------------------------------------------------------------------*/

// Implemented here for keeping it all inline (requires Internal::fixed).

inline int External::fixed (int elit) const {
  assert (elit);
  assert (elit != INT_MIN);
  int eidx = abs (elit);
  if (eidx > max_var) return 0;
  int ilit = e2i [eidx];
  if (!ilit) return 0;
  if (elit < 0) ilit = -ilit;
  return internal->fixed (ilit);
}

/*------------------------------------------------------------------------*/

// We want to have termination checks inlined, particularly the first
// function which appears in preprocessor loops.  Even though this first
// 'termination_forced' is set asynchronously, this should not lead to a
// data race issue (it also has been declared 'volatile').

inline bool Internal::terminated_asynchronously (int factor)
{
  // First way of asynchronous termination is through 'terminate' which sets
  // the 'termination_forced' flag directly.  The second way is through a
  // call back to a 'terminator' if it is non-zero, which however is costly.
  //
  if (termination_forced)
  {
    LOG ("termination asynchronously forced");
    return true;
  }

  // This is only for testing and debugging asynchronous termination calls.
  // In production code this could be removed but then should not be costly
  // and keeping it will allow to test correctness of asynchronous
  // termination on the production platform too.  After this triggers we
  // have to set the 'termination_forced' flag, such that subsequent calls
  // to this function do not check this again.
  //
  if (lim.terminate.forced) {
    assert (lim.terminate.forced > 0);
    if (lim.terminate.forced-- == 1) {
      LOG ("internally forcing termination");
      termination_forced = true;
      return true;
    }
    LOG ("decremented internal forced termination limit to %d",
      lim.terminate.forced);
  }

  // The second way of asynchronous termination is through registering and
  // calling an external 'Terminator' object.  This is of course more costly
  // than just checking a (volatile though) boolean flag, particularly in
  // tight loops.  To avoid this cost we only call the terminator in
  // intervals of 'opts.terminateint', which in addition can be scaled up by
  // the argument 'factor'.  If the terminator returns 'true' we set the
  // 'termination_forced' flag to 'true' in order to remember the
  // termination status and to avoid the terminator again.  Setting this
  // flag leads to the first test above to succeed in subsequent calls.
  //
  if (external->terminator && !lim.terminate.check--) {
    assert (factor > 0);
    assert (INT_MAX/factor > opts.terminateint);
    lim.terminate.check = factor * opts.terminateint;
    if (external->terminator->terminate ()) {
      termination_forced = true;                        // Cache it.
      LOG ("connected terminator forces termination");
      return true;
    }
  }

  return false;
}

/*------------------------------------------------------------------------*/

inline bool Internal::search_limits_hit ()
{
  assert (!preprocessing);
  assert (!localsearching);

  if (lim.conflicts >= 0 &&
      stats.conflicts >= lim.conflicts) {
    LOG ("conflict limit %" PRId64 " reached", lim.conflicts);
    return true;
  }

  if (lim.decisions >= 0 &&
      stats.decisions >= lim.decisions) {
    LOG ("decision limit %" PRId64 " reached", lim.decisions);
    return true;
  }

  return false;
}

/*------------------------------------------------------------------------*/

}

#endif
