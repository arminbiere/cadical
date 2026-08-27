#include "internal.hpp"
#include "flags.hpp"
#include "kitten.h"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/
static Clause external_reason_clause;

Internal::Internal ()
    : mode (SEARCH), unsat (0), iterating (false), localsearching (false),
      lookingahead (false), preprocessing (false),
      protected_reasons (false), force_saved_phase (false),
      searching_lucky_phases (false), stable (false), reported (false),
      external_prop (false), did_external_prop (false),
      external_prop_is_lazy (true), forced_backt_allowed (false),
      private_steps (false), out_of_order_level (-1),
      out_of_order_trail (-1), rephased (0), vsize (0), max_var (0),
      clause_id (0), original_id (0), reserved_ids (0), saved_decisions (0),
      concluded (false), lrat (false), frat (false),
      new_binary_since_dedup (true), level (0), vals (0), score_inc (1.0),
      scores (this), conflict (0), ignore (0),
      external_reason (&external_reason_clause), newest_clause (0),
      force_no_backtrack (false), from_propagator (false),
      ext_clause_forgettable (false), unsat_constraint (false),
      marked_failed (true), sweep_incomplete (false),
      earliest_changed_val (0), notified (0), notified_level (0),
      probe_reason (0), propagated (0), propagated2 (0), propergated (0),
      best_assigned (0), target_assigned (0), no_conflict_until (0),
      constraints_without_assumptions (0), randomized_deciding (false),
      constraint_cat (nullptr), cat (nullptr), num_assigned (0), proof (0),
      opts (this),
#ifndef QUIET
      profiles (this), force_phase_messages (false),
#endif
      arena (this), prefix ("c "), internal (this), external (0),
      termination_forced (false), vars (this->max_var),
      lits (this->max_var) {
  control.emplace_back (0, 0);

  // The 'dummy_binary' is used in 'try_to_subsume_clause' to fake a real
  // clause (which then can be used to subsume or strengthen the given
  // clause in one routine for both binary and non binary clauses) and
  // in walk (which is only used as a placeholder in the watch lists
  // when logging is off, since the clause is not accessed).  This
  // fake binary clause is always kept non-redundant (and not-moved etc.)
  // due to the following 'memset'.  Only literals will be changed.

  // In a previous version we used local automatic allocated 'Clause' on the
  // stack, which became incompatible with several compilers (see the
  // discussion on flexible array member in 'Clause.cpp').

  size_t bytes = Clause::bytes (2);
  dummy_binary = (Clause *) new char[bytes];
  memset (dummy_binary, 0, bytes);
  dummy_binary->size = 2;

  /*with C++17: static_*/ assert (max_used == (1 << USED_SIZE) - 1);
}

Internal::~Internal () {
  delete[] (char *) dummy_binary;
  for (const auto &c : clauses)
    delete_clause (c);
  if (proof)
    delete proof;
  for (auto &tracer : tracers)
    delete tracer;
  for (auto &filetracer : file_tracers)
    delete filetracer;
  for (auto &stattracer : stat_tracers)
    delete stattracer;
  if (vals) {
    vals -= vsize;
    delete[] vals;
  }
  if (constraint_cat)
    KITTEN_NAMESPACE (kitten_release (constraint_cat));
}

/*------------------------------------------------------------------------*/

// Values in 'vals' can be accessed in the range '[-max_var,max_var]' that
// is directly by a literal.  This is crucial for performance.  By shifting
// the start of 'vals' appropriately, we achieve that negative offsets from
// the start of 'vals' can be used.  We also need to set both values at
// 'lit' and '-lit' during assignments.  In MiniSAT integer literals are
// encoded, using the least significant bit as negation.  This avoids taking
// the 'abs ()' (as in our solution) and thus also avoids a branch in the
// hot-spot of the solver (clause traversal in propagation).  That solution
// requires another (branch less) negation of the values though and
// debugging is harder since literals occur only encoded in clauses.
// The main draw-back of our solution is that we have to shift the memory
// and access it through negative indices, which looks less clean (but still
// as far I can tell is properly defined C / C++).

void Internal::enlarge_vals (size_t new_vsize) {
  signed char *new_vals;
  const size_t bytes = 2u * new_vsize;
  new_vals = new signed char[bytes]; // g++-4.8 does not like ... { 0 };
  memset (new_vals, 0, bytes);
  new_vals += new_vsize;

  if (vals) {
    memcpy (new_vals - max_var, vals - max_var, 2u * max_var + 1u);
    vals -= vsize;
    delete[] vals;
  } else
    assert (!vsize);
  vals = new_vals;
}

/*------------------------------------------------------------------------*/
// This function enlarges all data structures. You should use it only if you
// add many literals at once. Otherwise, use `reserve_vars` followed by
// importing all variables.
//
// Remark: for the first literal we cannot distinguish between not watching
// and watching. Therefore, we resize the watch lists, because we are
// watching anyway.
void Internal::enlarge (int new_max_var) {
  // New variables can be created that can invoke enlarge anytime (via calls
  // during ipasir-up call-backs), thus assuming (!level) is not correct
  size_t new_vsize = vsize ? vsize : 1 + (size_t) new_max_var;
  while (new_vsize <= (size_t) new_max_var)
    new_vsize *= 2;
  LOG ("enlarge internal size from %zd to new size %zd", vsize, new_vsize);
  // Ordered in the size of allocated memory (larger block first).
  if (lrat || frat)
    enlarge_zero (unit_clause_idx, 2 * new_vsize);
  if (!vsize || watching ())
    enlarge_init (wtab, 2 * new_vsize, {});
  if (!otab.empty ())
    enlarge_init (otab, 2 * new_vsize, Occs ());
  if (!ntab.empty ())
    enlarge_zero (ntab, 2 * new_vsize);
  enlarge_only (vtab, new_vsize);
  enlarge_zero (parents, new_vsize);
  enlarge_only (links, new_vsize);
  enlarge_zero (btab, new_vsize);
  enlarge_zero (gtab, new_vsize);
  enlarge_zero (stab, new_vsize);
  enlarge_init (ptab, 2 * new_vsize, -1);
  enlarge_only (ftab, new_vsize);
  if (external)
    enlarge_zero (relevanttab, new_vsize);
  const signed char val = opts.phase ? 1 : -1;
  enlarge_init (phases.saved, new_vsize, val);
  enlarge_zero (phases.forced, new_vsize);
  enlarge_zero (phases.target, new_vsize);
  enlarge_zero (phases.best, new_vsize);
  enlarge_zero (phases.prev, new_vsize);
  enlarge_zero (marks, new_vsize);
  // keep this last to avoid memory issues on deallocation.
  enlarge_vals (new_vsize);
  vsize = new_vsize;
}

// This function enlarges enough to do backtracking (without updating the
// phases only!) and (if needed) watched and occurrence table, but it does
// not enlarge everything. This is done later when importing all variables.
// It does enlarge watch lists (only if you watching) and occurrence lists
// (only if you are having occs).
//
// Remark: for the first literal we cannot distinguish between not watching
// and watching. Therefore, we resize the watch lists, because we are
// watching anyway.
void Internal::reserve_vars (int new_min_vsize) {
  if ((size_t) new_min_vsize < vsize)
    return;
  size_t new_vsize = vsize ? 2 * vsize : 1 + (size_t) max_var;
  while (new_vsize <= (size_t) new_min_vsize)
    new_vsize *= 2;

  LOG ("reserving %d new internal variables, reserved so far: %d",
       (int) new_vsize - max_var, max_var);

  if (lrat || frat)
    enlarge_zero (unit_clause_idx, 2 * new_vsize);
  // keep this before enlarge_vals
  if (!vsize || watching ()) {
    enlarge_only (wtab, 2 * new_vsize);
  }
  if (!otab.empty ())
    enlarge_init (otab, 2 * new_vsize, Occs ());
  if (!ntab.empty ())
    enlarge_zero (ntab, 2 * new_vsize);
  enlarge_only (vtab, new_vsize);
  enlarge_zero (btab, new_vsize);
  enlarge_zero (stab, new_vsize);
  enlarge_only (ftab, new_vsize);
  if (external)
    enlarge_zero (relevanttab, new_vsize);
  enlarge_only (phases.saved, new_vsize);
  enlarge_zero (marks, new_vsize);
  // keep this last to avoid memory issues on deallocation.
  enlarge_vals (new_vsize);
  vsize = new_vsize;
}

void Internal::add_original_lit (int lit) {
  assert (abs (lit) <= max_var);
  if (lit) {
    original.push_back (lit);
  } else {
    const int64_t id =
        original_id < reserved_ids ? ++original_id : ++clause_id;
    if (proof) {
      // Use the external form of the clause for printing in proof
      // Externalize(internalized literal) != external literal
      assert (!original.size () || !external->eclause.empty ());
      proof->add_external_original_clause (id, false, external->eclause);
    }
    if (internal->opts.check &&
        (internal->opts.checkwitness || internal->opts.checkfailed)) {
      bool forgettable = from_propagator && ext_clause_forgettable;
      if (forgettable && opts.check) {
        assert (!original.size () || !external->eclause.empty ());

        // First integer is the presence-flag (even if the clause is empty)
        external->forgettable_original[id] = {1};

        for (auto const &elit : external->eclause)
          external->forgettable_original[id].push_back (elit);

        LOG (external->eclause,
             "clause added to external forgettable map:");
      }
    }

    add_new_original_clause (id);
    original.clear ();
  }
}

void Internal::finish_added_clause_with_id (int64_t id, bool restore) {
  if (proof) {
    // Use the external form of the clause for printing in proof
    // Externalize(internalized literal) != external literal
    assert (!original.size () || !external->eclause.empty ());
    proof->add_external_original_clause (id, false, external->eclause,
                                         restore);
  }
  add_new_original_clause (id);
  original.clear ();
}

/*------------------------------------------------------------------------*/

void Internal::reserve_ids (int number) {
  // return;
  LOG ("reserving %d ids", number);
  assert (number >= 0);
  assert (!clause_id && !reserved_ids && !original_id);
  clause_id = reserved_ids = number;
  if (proof)
    proof->begin_proof (reserved_ids);
}

/*------------------------------------------------------------------------*/

#ifdef PROFILE_MODE

// Separating these makes it easier to profile stable and unstable search.

bool Internal::propagate_wrapper () {
  if (stable)
    return propagate_stable ();
  else
    return propagate_unstable ();
}

void Internal::analyze_wrapper () {
  if (stable)
    analyze_stable ();
  else
    analyze_unstable ();
}

int Internal::decide_wrapper () {
  if (stable)
    return decide_stable ();
  else
    return decide_unstable ();
}

#endif

/*------------------------------------------------------------------------*/

// This is the main CDCL loop with interleaved inprocessing.

int Internal::cdcl_loop_with_inprocessing () {

  int res = 0;

  PROFILE_SCOPE_SEARCH (search, stable);

  if (stable) {
    report ('[');
  } else {
    report ('{');
  }

  while (!res) {
    if (unsat)
      res = 20;
    else if (unsat_constraint)
      res = 20;
    else if (!propagate_wrapper ())
      analyze_wrapper (); // propagate and analyze
    else if (iterating)
      iterate ();                          // report learned unit
    else if (terminated_asynchronously ()) // externally terminated
      break;
    else if (!external_propagate () || unsat) { // external propagation
      if (unsat)
        continue;
      else
        analyze ();
    } else if (satisfied ()) { // found model
      if (!external_check_solution () || unsat) {
        if (unsat)
          continue;
        else
          analyze ();
      } else if (satisfied ())
        res = 10;
    } else if (search_limits_hit ())
      break;                               // decision or conflict limit
    else if (terminated_asynchronously ()) // externally terminated
      break;
    else if (restarting ())
      restart (); // restart by backtracking
    else if (rephasing ())
      rephase (); // reset variable phases
    else if (reducing ())
      reduce (); // collect useless clauses
    else if (inprobing ())
      inprobe (); // schedule of inprocessing
    else if (ineliminating ())
      elim (); // variable elimination
    else if (compacting ())
      compact (); // collect variables
    else if (conditioning ())
      condition (); // globally blocked clauses
    else
      res = decide (); // next decision
  }

  if (stable) {
    report (']');
  } else {
    report ('}');
  }

  return res;
}

int Internal::propagate_assumptions () {
  activating_all_new_imported_literals ();
  if (proof)
    proof->solve_query ();
  if (opts.ilb) {
    sort_and_reuse_assumptions ();
    assert (opts.ilb == 2 || (size_t) level <= assumptions.size ());
    stats.ilb_triggers++;
    stats.ilb_success += (level > 0);
    stats.ilb_reuse_levels += level;
    if (level) {
      assert (control.size () > 1);
      stats.ilb_reuse_literals += num_assigned - control[1].trail;
    }
  }
  init_search_limits ();
  init_report_limits ();

  int res = already_solved (); // root-level propagation is done here

  int last_assumption_level = assumptions.size ();
  last_assumption_level += constraints_without_assumptions;

  if (!res) {
    restore_clauses ();
    while (!res) {
      if (unsat)
        res = 20;
      else if (unsat_constraint)
        res = 20;
      else if (!propagate ()) {
        // let analyze run to get failed assumptions
        analyze ();
      } else if (!external_propagate () || unsat) { // external propagation
        if (unsat)
          continue;
        else
          analyze ();
      } else if (satisfied ()) { // found model
        if (!external_check_solution () || unsat) {
          if (unsat)
            continue;
          else
            analyze ();
        } else if (satisfied ())
          res = 10;
      } else if (search_limits_hit ())
        break;                               // decision or conflict limit
      else if (terminated_asynchronously ()) // externally terminated
        break;
      else {
        if (level >= last_assumption_level)
          break;
        res = decide ();
      }
    }
  }

  if (unsat || unsat_constraint)
    res = 20;

  if (!res && satisfied ())
    res = 10;

  finalize (res);
  reset_solving ();
  report_solving (res);

  return res;
}

void Internal::implied (std::vector<int> &entrailed) {
  int last_assumption_level = assumptions.size ();
  last_assumption_level += constraint_vars.size ();

  size_t trail_limit = trail.size ();
  if (level > last_assumption_level)
    trail_limit = control[last_assumption_level + 1].trail;

  for (size_t i = 0; i < trail_limit; i++)
    entrailed.push_back (trail[i]);
}

/*------------------------------------------------------------------------*/

// Most of the limits are only initialized in the first 'solve' call and
// increased as in a stand-alone non-incremental SAT call except for those
// explicitly marked as being reset below.

void Internal::init_report_limits () {
  reported = false;
  lim.report = 0;
  lim.recompute_tier = 5000;
}

void Internal::init_preprocessing_limits () {

  const bool incremental = lim.initialized;
  if (incremental)
    LOG ("reinitializing preprocessing limits incrementally");
  else
    LOG ("initializing preprocessing limits and increments");

  const char *mode = 0;

  /*----------------------------------------------------------------------*/

  if (incremental)
    mode = "keeping";
  else {
    last.elim.marked = -1;
    lim.elim = stats.conflicts + scale (opts.elimint);
    mode = "initial";
  }
  (void) mode;
  LOG ("%s elim limit %" PRId64 " after %" PRId64 " conflicts", mode,
       lim.elim, lim.elim - stats.conflicts);

  // Initialize and reset elimination bounds in any case.

  lim.elimbound = opts.elimboundmin;
  LOG ("elimination bound %" PRId64 "", lim.elimbound);

  /*----------------------------------------------------------------------*/

  if (!incremental) {

    last.ternary.marked = -1; // TODO this should not be necessary...

    lim.compact = stats.conflicts + opts.compactint;
    LOG ("initial compact limit %" PRId64 " increment %" PRId64 "",
         lim.compact, lim.compact - stats.conflicts);
  }

  /*----------------------------------------------------------------------*/

  if (incremental)
    mode = "keeping";
  else {
    double delta =
        stats.clauses_irredundant ? log10 (stats.clauses_irredundant) : 100;
    delta = delta * delta;
    lim.inprobe = stats.conflicts + opts.inprobeint * delta;
    mode = "initial";
  }
  (void) mode;
  LOG ("%s probe limit %" PRId64 " after %" PRId64 " conflicts", mode,
       lim.inprobe, lim.inprobe - stats.conflicts);

  /*----------------------------------------------------------------------*/

  if (incremental)
    mode = "keeping";
  else {
    lim.condition = stats.conflicts + opts.conditionint;
    mode = "initial";
  }
  LOG ("%s condition limit %" PRId64 " increment %" PRId64, mode,
       lim.condition, lim.condition - stats.conflicts);

  /*----------------------------------------------------------------------*/

  // Initial preprocessing rounds.

  if (inc.preprocessing <= 0) {
    lim.preprocessing = 0;
    LOG ("no preprocessing");
  } else {
    lim.preprocessing = inc.preprocessing;
    LOG ("limiting to %" PRId64 " preprocessing rounds", lim.preprocessing);
  }
#ifndef LOGGING
  (void) mode;
#endif
}

void Internal::init_search_limits () {

  const bool incremental = lim.initialized;
  if (incremental)
    LOG ("reinitializing search limits incrementally");
  else
    LOG ("initializing search limits and increments");

  const char *mode = 0;

  /*----------------------------------------------------------------------*/

  if (incremental)
    mode = "keeping";
  else {
    last.reduce.conflicts = -1;
    lim.reduce = stats.conflicts + opts.reduceinit;
    mode = "initial";
  }
  (void) mode;
  LOG ("%s reduce limit %" PRId64 " after %" PRId64 " conflicts", mode,
       lim.reduce, lim.reduce - stats.conflicts);

  /*----------------------------------------------------------------------*/

  if (incremental)
    mode = "keeping";
  else {
    lim.flush = opts.flushint;
    inc.flush = opts.flushint;
    mode = "initial";
  }
  (void) mode;
  LOG ("%s flush limit %" PRId64 " interval %" PRId64 "", mode, lim.flush,
       inc.flush);

  /*----------------------------------------------------------------------*/

  // Initialize or reset 'rephase' limits in any case.

  lim.rephase = stats.conflicts + opts.rephaseint;
  lim.rephased[0] = lim.rephased[1] = 0;
  last.stabilize.rephased = 0;
  LOG ("new rephase limit %" PRId64 " after %" PRId64 " conflicts",
       lim.rephase, lim.rephase - stats.conflicts);

  /*----------------------------------------------------------------------*/

  // Initialize or reset 'restart' limits in any case.

  lim.restart = stats.conflicts + opts.restartint;
  LOG ("new restart limit %" PRId64 " increment %" PRId64 "", lim.restart,
       lim.restart - stats.conflicts);

  /*----------------------------------------------------------------------*/

  if (!incremental) {
    stable = opts.stabilize && opts.stabilizeonly;
    if (stable)
      LOG ("starting in always forced stable phase");
    else
      LOG ("starting in default non-stable phase");
    init_averages ();
  } else if (opts.stabilize && opts.stabilizeonly) {
    LOG ("keeping always forced stable phase");
    assert (stable);
  } else if (stable) {
    LOG ("switching back to default non-stable phase");
    stable = false;
    swap_averages ();
  } else
    LOG ("keeping non-stable phase");

  inc.stabilize = 0;
  last.stabilize.conflicts = stats.conflicts;
  lim.stabilize = stats.conflicts + opts.stabilizeinit;
  last.stabilize.ticks = stats.ticks_search_unstable;
  stats.stable_phases_current = 0;
  LOG ("new ticks-based stabilize limit %" PRId64 " after %d conflicts",
       lim.stabilize, (int) opts.stabilizeinit);

  if (opts.stabilize && opts.reluctant && opts.reluctantint) {
    LOG ("new restart reluctant doubling sequence period %d",
         opts.reluctant);
    reluctant.enable (opts.reluctantint, opts.reluctantmax);
  } else
    reluctant.disable ();

  /*----------------------------------------------------------------------*/

  // Conflict and decision limits.

  if (inc.conflicts < 0) {
    lim.conflicts = -1;
    LOG ("no limit on conflicts");
  } else {
    lim.conflicts = stats.conflicts + inc.conflicts;
    LOG ("conflict limit after %" PRId64 " conflicts at %" PRId64
         " conflicts",
         inc.conflicts, lim.conflicts);
  }

  if (inc.decisions < 0) {
    lim.decisions = -1;
    LOG ("no limit on decisions");
  } else {
    lim.decisions = stats.decisions + inc.decisions;
    LOG ("decision limit after %" PRId64 " decisions at %" PRId64
         " decisions",
         inc.decisions, lim.decisions);
  }

  if (inc.ticks < 0) {
    lim.ticks = -1;
    LOG ("no limit on ticks");
  } else {
    lim.ticks =
        stats.ticks_search_unstable + stats.ticks_search_stable + inc.ticks;
    LOG ("ticks limit after %" PRId64 " ticks at %" PRId64 " ticks",
         inc.ticks, lim.ticks);
  }

  /*----------------------------------------------------------------------*/

  // Initial preprocessing rounds.

  if (inc.localsearch <= 0) {
    lim.localsearch = 0;
    LOG ("no local search");
  } else {
    lim.localsearch = inc.localsearch;
    LOG ("limiting to %" PRId64 " local search rounds", lim.localsearch);
  }

  /*----------------------------------------------------------------------*/
  // tier 1 and tier 2 limits
  if (incremental && opts.recomputetier) {
    for (auto m : {true, false})
      for (auto &u : stats.used[m])
        u = 0;
    stats.bump_used[0] = 0;
    stats.bump_used[1] = 0;
    for (auto u : {true, false}) {
      tier1[u] = max (tier1[u], opts.tier1minglue ? opts.tier1minglue : 2);
      tier2[u] = max (tier2[u], opts.tier2minglue ? opts.tier2minglue : 6);
    }
    stats.recomputed_tiers = 0;
  }

  /*----------------------------------------------------------------------*/
  // clause decaying
  if (incremental)
    last.incremental_decay.last_id = 0;
  else {
    lim.incremental_decay = opts.incdecayint;
  }

  /*----------------------------------------------------------------------*/

  if (incremental)
    mode = "keeping";
  else {
    lim.random_decision = stats.conflicts + opts.randecinit;
    mode = "initial";
  }
  (void) mode;
  LOG ("%s randomize decision limit %" PRId64 " after %" PRId64
       " conflicts",
       mode, lim.random_decision, lim.random_decision - stats.conflicts);

  /*----------------------------------------------------------------------*/

  lim.initialized = true;
}

/*------------------------------------------------------------------------*/

bool Internal::preprocess_round (int round, bool &triggered) {
  (void) round;
  if (unsat)
    return false;
  if (!max_var)
    return false;
  if (terminated_asynchronously ())
    return false;
  PROFILE_SCOPE (preprocess);
  if (!triggered)
    report ('('), triggered = true;
  struct {
    int64_t vars, clauses;
  } before, after;
  before.vars = active ();
  before.clauses = stats.clauses_now_irr;
  stats.preprocessings++;
  assert (!preprocessing);
  preprocessing = true;
  PHASE ("preprocessing", stats.preprocessings,
         "starting round %d with %" PRId64 " variables and %" PRId64
         " clauses",
         round, before.vars, before.clauses);
  int old_elimbound = lim.elimbound;
  int old_eliminated = stats.vars_all_elim;
  if (opts.inprobing)
    inprobe (false);
  if (opts.elim)
    elim (false);
  if (opts.condition)
    condition (false);
  after.vars = active ();
  after.clauses = stats.clauses_now_irr;
  assert (preprocessing);
  preprocessing = false;
  PHASE ("preprocessing", stats.preprocessings,
         "finished round %d with %" PRId64 " variables and %" PRId64
         " clauses",
         round, after.vars, after.clauses);
  report ('P');
  if (unsat)
    return false;
  if (after.vars != before.vars)
    return true;
  if (old_elimbound < lim.elimbound)
    return true;
  if (old_eliminated < stats.vars_all_elim)
    return true;
  return false;
}

// for now counts as one of the preprocessing rounds TODO: change this?
void Internal::preprocess_quickly (bool always, bool &triggered) {
  if (unsat)
    return;
  if (!max_var)
    return;
  if (terminated_asynchronously ())
    return;
  if (!opts.preprocesslight)
    return;
  if (!always && stats.searches > 1)
    return;
  PROFILE_SCOPE (preprocess);
#ifndef QUIET
  struct {
    int64_t vars, clauses;
  } before, after;
  before.vars = active ();
  before.clauses = stats.clauses_now_irr;
#endif
  // stats.preprocessings++;
  assert (!preprocessing);
  preprocessing = true;
  triggered = true;
  report ('(');
  PHASE ("preprocessing", stats.preprocessings,
         "starting with %" PRId64 " variables and %" PRId64 " clauses",
         before.vars, before.clauses);
  if (extract_gates (true))
    decompose ();
  binary_clauses_backbone ();
  if (sweep ())
    decompose ();
  mark_duplicated_binary_clauses_as_garbage ();
  factor ();

  if (opts.fastelim)
    elimfast ();

  // if (opts.fastelim)
  //  elimfast ();
  // if (opts.condition)
  // condition (false);
#ifndef QUIET
  after.vars = active ();
  after.clauses = stats.clauses_now_irr;
#endif
  assert (preprocessing);
  preprocessing = false;
  PHASE ("preprocessing", stats.preprocessings,
         "finished with %" PRId64 " variables and %" PRId64 " clauses",
         after.vars, after.clauses);
  report ('P');
}

int Internal::preprocess (bool always) {
  int res = 0;
  if (res)
    return res;
  bool preprecessing_triggered = false;

  if (opts.deduplicateallinit && !stats.deduplicate_rounds)
    deduplicate_all_clauses ();
  preprocess_quickly (always, preprecessing_triggered);
  for (int i = 0; i < lim.preprocessing; i++)
    if (!preprocess_round (i, preprecessing_triggered))
      break;
  if (preprecessing_triggered)
    report (')');
  if (unsat)
    return 20;
  return 0;
}

/*------------------------------------------------------------------------*/

int Internal::try_to_satisfy_formula_by_saved_phases () {
  LOG ("satisfying formula by saved phases");
  assert (!level);
  assert (!force_saved_phase);
  assert (propagated == trail.size ());
  force_saved_phase = true;
  if (external_prop) {
    assert (!level);
    LOG ("external notifications are turned off during preprocessing.");
    private_steps = true;
  }
  int res = 0;
  while (!res) {
    if (satisfied ()) {
      LOG ("formula indeed satisfied by saved phases");
      res = 10;
    } else if (decide ()) {
      LOG ("inconsistent assumptions with redundant clauses and phases");
      res = 20;
    } else if (!propagate ()) {
      LOG ("saved phases do not satisfy redundant clauses");
      assert (level > 0);
      backtrack ();
      conflict = 0; // ignore conflict
      assert (!res);
      break;
    }
  }
  assert (force_saved_phase);
  force_saved_phase = false;
  if (external_prop) {
    private_steps = false;
    LOG ("external notifications are turned back on.");
    if (!level)
      notify_assignments (); // In case fixed assignments were found.
    else {
      renotify_trail_after_local_search ();
    }
  }
  return res;
}

/*------------------------------------------------------------------------*/

void Internal::produce_failed_assumptions () {
  LOG ("producing failed assumptions");
  assert (!level);
  assert (!assumptions.empty ());
  while (!unsat) {
    assert (!satisfied ());
    notify_assignments ();
    if (decide ())
      break;
    while (!unsat && !propagate ())
      analyze ();
  }
  notify_assignments ();
  if (unsat)
    LOG ("formula is actually unsatisfiable unconditionally");
  else
    LOG ("assumptions indeed failing");
}

/*------------------------------------------------------------------------*/

int Internal::local_search_round (int round) {

  assert (round > 0);

  if (unsat)
    return false;
  if (!max_var)
    return false;
  if (terminated_asynchronously ())
    return false;

  MODE_SCOPE_WALK (WALK);
  PROFILE_SCOPE_WALK (walk);
  assert (!localsearching);
  localsearching = true;

  // Determine propagation limit quadratically scaled with rounds.
  //
  int64_t limit = opts.walkmineffinit;
  limit *= round;
  if (LONG_MAX / round > limit)
    limit *= round;
  else
    limit = LONG_MAX;

  int res;
  if (opts.walkfullocc == 1)
    res = walk_full_occs_round (limit, true);
  else if (opts.walkfullocc == 2)
    res = walk_ddfw_round (limit, true);
  else
    res = walk_round (limit, true);

  assert (localsearching);
  localsearching = false;
  report ('L');

  return res;
}

int Internal::local_search () {

  if (unsat)
    return 0;
  if (!max_var)
    return 0;
  if (!opts.walk)
    return 0;
  if (constraint_cat)
    return 0;
  if (!lim.localsearch)
    return 0;

  int res = 0;
  assert (imports.empty ());
  assert (!level);

  for (int i = 1; !res && i <= lim.localsearch; i++)
    res = local_search_round (i);

  if (res == 10) {
    LOG ("local search determined formula to be satisfiable");
    assert (!stats.walk_minimum);
    res = try_to_satisfy_formula_by_saved_phases ();
  } else if (res == 20) {
    LOG ("local search determined assumptions to be inconsistent");
    assert (!assumptions.empty ());
  }

  return res;
}

/*------------------------------------------------------------------------*/

// if preprocess_only is false and opts.ilb is true we do not preprocess
// such that we do not have to backtrack to level 0.
//
int Internal::solve (bool preprocess_only) {
  assert (clause.empty ());
  stats.searches++;
  PROFILE_SCOPE (solve);
  activating_all_new_imported_literals ();
  if (proof)
    proof->solve_query ();
  if (opts.ilb) {
    sort_and_reuse_assumptions ();
    assert (opts.ilb || (size_t) level <= assumptions.size ());
    stats.ilb_triggers++;
    stats.ilb_success += (level > 0);
    stats.ilb_reuse_levels += level;
    if (level) {
      assert (control.size () > 1);
      stats.ilb_reuse_literals += num_assigned - control[1].trail;
    }
    if (external->propagator)
      renotify_trail_after_ilb ();
  }
  if (preprocess_only)
    LOG ("internal solving in preprocessing only mode");
  else
    LOG ("internal solving in full mode");
  init_report_limits ();
  int res = already_solved ();
  if (!res && preprocess_only && level)
    backtrack ();
  if (!res)
    res = restore_clauses ();
  if (!res || (res == 10 && external_prop)) {
    init_preprocessing_limits ();
    if (!preprocess_only)
      init_search_limits ();
  }
  if (!preprocess_only) {
    if (!res && !level)
      res = local_search ();
  }
  bool run_lucky = stats.conflicts >=
                   lim.lucky; // cannot be in lucky, because we run it twice
  bool update_lucky_limits =
      !opts.luckylate; // update in the second run if there is any
  if (!preprocess_only && !res && !level && opts.luckyearly && run_lucky)
    res = lucky_phases (update_lucky_limits);
  if (!res && !level)
    res = preprocess (preprocess_only);
  if (!preprocess_only) {
    if (!res && !level && opts.luckylate && run_lucky)
      res = lucky_phases (true);
    if (!res && !level)
      res = local_search ();
    if (!res)
      decay_clauses_upon_incremental_clauses ();
    if (!res || (res == 10 && external_prop)) {
      if (res == 10 && external_prop && level)
        backtrack ();
      res = cdcl_loop_with_inprocessing ();
    }
  }
  finalize (res);
  reset_solving ();
  report_solving (res);
  return res;
}

int Internal::already_solved () {
  int res = 0;
  if (unsat || unsat_constraint) {
    LOG ("already inconsistent");
    res = 20;
  } else {
    if (level && !opts.ilb)
      backtrack ();
    if (!level && !propagate ()) {
      LOG ("root level propagation produces conflict");
      learn_empty_clause ();
      res = 20;
    }
    if (max_var == 0 && res == 0)
      res = 10;
  }
  return res;
}
void Internal::report_solving (int res) {
  if (res == 10)
    report ('1');
  else if (res == 20)
    report ('0');
  else
    report ('?');
}

void Internal::reset_solving () {
  if (termination_forced) {

    // TODO this leads potentially to a data race if the external
    // user is calling 'terminate' twice within one 'solve' call.
    // A proper solution would be to guard / protect setting the
    // 'termination_forced' flag and only allow it during solving and
    // ignore it otherwise thus also the second time it is called during a
    // 'solve' call.  We could move resetting it also the start of
    // 'solve'.
    //
    termination_forced = false;

    LOG ("reset forced termination");
  }
}

int Internal::restore_clauses () {
  int res = 0;
  if (opts.restoreall <= 1 && external->tainted.empty ()) {
    LOG ("no tainted literals and nothing to restore");
    report ('*');
  } else {
    report ('+');
    // remove_garbage_binaries ();
    external->restore_clauses ();
    internal->report ('r');
    if (!unsat && !level && !propagate ()) {
      LOG ("root level propagation after restore produces conflict");
      learn_empty_clause ();
      res = 20;
    }
  }
  return res;
}

int Internal::lookahead () {
  assert (clause.empty ());
  PROFILE_SCOPE (lookahead);
  assert (!lookingahead);
  lookingahead = true;
  activating_all_new_imported_literals ();
  if (external_prop) {
    if (level) {
      // Combining lookahead with external propagator is limited
      // Note that lookahead_probing (); would also force backtrack anyway
      backtrack ();
    }
    LOG ("external notifications are turned off during preprocessing.");
    private_steps = true;
  }
  int tmp = already_solved ();
  if (!tmp)
    tmp = restore_clauses ();
  int res = 0;
  if (!tmp)
    res = lookahead_probing ();
  if (res == INT_MIN)
    res = 0;
  reset_solving ();
  report_solving (tmp);
  assert (lookingahead);
  lookingahead = false;
  PROFILE_SCOPE_EARLY_EXIT (lookahead);
  if (external_prop) {
    private_steps = false;
    LOG ("external notifications are turned back on.");
    notify_assignments (); // In case fixed assignments were found.
  }
  return res;
}

/*------------------------------------------------------------------------*/

void Internal::finalize (int res) {
  if (!proof)
    return;
  LOG ("finalizing result %d", res);
  // finalize external units
  if (frat) {
    for (const auto &evar : external->vars) {
      assert (evar > 0);
      const auto eidx = 2 * evar;
      int sign = 1;
      int64_t id = external->ext_units[eidx];
      if (!id) {
        sign = -1;
        id = external->ext_units[eidx + 1];
      }
      if (id) {
        proof->finalize_external_unit (id, evar * sign);
      }
    }
    // finalize internal units
    for (const auto &lit : lits) {
      const auto elit = externalize (lit);
      if (elit) {
        const unsigned eidx = (elit < 0) + 2u * (unsigned) abs (elit);
        const int64_t id = external->ext_units[eidx];
        if (id) {
          assert (unit_clauses (vlit (lit)) == id);
          continue;
        }
      }
      const int64_t id = unit_clauses (vlit (lit));
      if (!id)
        continue;
      proof->finalize_unit (id, lit);
    }
    // See the discussion in 'propagate' on why garbage binary clauses stick
    // around.
    for (const auto &c : clauses)
      if (!c->garbage || (c->size == 2 && !c->flushed))
        proof->finalize_clause (c);

    // finalize conflict and proof
    if (unsat) {
      proof->finalize_clause (unsat, {});
    }
  }
  proof->report_status (res, unsat);
  if (res == 10)
    external->conclude_sat ();
  else if (res == 20)
    conclude_unsat ();
  else // if (!res) -> res can be -1 as well
    external->conclude_unknown ();
}

/*------------------------------------------------------------------------*/

void Internal::print_statistics () {
  stats.print (this);
  for (auto &st : stat_tracers)
    st->print_stats ();
}

/*------------------------------------------------------------------------*/

// Only useful for debugging purposes.

void Internal::dump (Clause *c) {
  for (const auto &lit : *c)
    printf ("%d ", lit);
  printf ("0\n");
}

void Internal::dump () {
  int64_t m = assumptions.size ();
  for (auto idx : vars)
    if (fixed (idx))
      m++;
  for (const auto &c : clauses)
    if (!c->garbage)
      m++;
  printf ("p cnf %d %" PRId64 "\n", max_var, m);
  for (auto idx : vars) {
    const int tmp = fixed (idx);
    if (tmp)
      printf ("%d 0\n", tmp < 0 ? -idx : idx);
  }
  for (const auto &c : clauses)
    if (!c->garbage)
      dump (c);
  for (const auto &lit : assumptions)
    printf ("%d 0\n", lit);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/

bool Internal::traverse_constraint (ClauseIterator &it) {
  if (constraints.empty ())
    return true;

  vector<int> eclause;
  if (unsat)
    return it.clause (eclause);

  LOG (constraints, "traversing constraints");
  bool satisfied = false;
  for (auto ilit : constraints) {
    const int tmp = fixed (ilit);
    if (tmp > 0) {
      satisfied = true;
      break;
    }
    if (tmp < 0)
      continue;
    const int elit = externalize (ilit);
    if (elit)
      eclause.push_back (elit);
    else {
      if (!satisfied && !it.clause (eclause))
        return false;
      eclause.clear ();
      satisfied = false;
    }
  }

  return true;
}
/*------------------------------------------------------------------------*/

bool Internal::traverse_clauses (ClauseIterator &it) {
  vector<int> eclause;
  if (unsat)
    return it.clause (eclause);
  for (const auto &c : clauses) {
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    bool satisfied = false;
    for (const auto &ilit : *c) {
      const int tmp = fixed (ilit);
      if (tmp > 0) {
        satisfied = true;
        break;
      }
      if (tmp < 0)
        continue;
      const int elit = externalize (ilit);
      eclause.push_back (elit);
    }
    if (!satisfied && !it.clause (eclause))
      return false;
    eclause.clear ();
  }
  return true;
}

void Internal::declare_variable (int ilit) {
  reserve_vars (ilit);
  assert ((size_t) ilit < vsize);
  if (ilit >= max_var) {
    stats.vars_unused += (ilit - max_var);
    stats.vars_inactive += (ilit - max_var);
    max_var = ilit;
  }
  Flags &f = internal->flags (ilit);
  if (f.declared ())
    return;

  LOG ("declaring %s", LOGLIT (ilit));
  mark_declared (ilit);
  imports.push_back (ilit);
}

// Now we come to the part where we import literals. We either import
// them in order of appearance, in order of numbering, or the reversed
// versions of that. The sorting is based on the external ordering not
// the internal ordering.
void Internal::activating_all_new_imported_literals () {
  LOG (imports, "activating all new variables");
  if (imports.empty ())
    return;
  if (opts.varindexorder)
    std::sort (begin (imports), end (imports), [&] (int l, int o) {
      return i2e[vidx (l)] < i2e[vidx (o)];
    });
  if (!opts.varprioritizefirst)
    std::reverse (begin (imports), end (imports));
  auto max_it =
      std::max_element (imports.begin (), imports.end (),
                        [] (int a, int b) { return abs (a) < abs (b); });
  assert (max_it != imports.end ());
  int new_max_var = vidx (*max_it);
  enlarge (new_max_var);

  for (auto lit : imports) {
    int idx = vidx (lit);
    auto &f = flags (idx);
    // the user asked for it but did not put the literal in any
    // clause, we still should declare it (for future use by the user)
    if (f.unused ())
      mark_declared (idx);
    // for units, we do have to enqueue (in case we backtracked and already
    // added it)
    if (f.fixed ()) {
      continue;
    }

    if (f.declared ())
      mark_active (idx);
    // otherwise, reactivating literal
    init_enqueue (idx);

    // due to propagation and backtracking, the literal might have already
    // been added
    if (!scores.contains (idx)) {
      LOG ("pushing %s to the scores", LOGLIT (idx));
      scores.push_back (idx);
    }
    assert (scores.contains (idx));
    assert (f.active () || f.fixed ());
  }

  stats.vars += imports.size ();
  imports.clear ();
  check_var_stats ();
#ifndef NDEBUG
  for (auto c : clauses) {
    if (c->garbage)
      continue;
    for (auto lit : *c) {
      assert (flags (lit).active () || flags (lit).fixed () ||
              flags (lit).eliminated ());
    }
  }
  for (auto v : vars) {
    assert (flags (v).unused () || internal->val (v) ||
            scores.contains (v));
    if (flags (v).unused ())
      assert (!scores.contains (v));
  }
  check_queue ();
#endif
}
} // namespace CaDiCaL
