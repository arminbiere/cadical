#include "internal.hpp"
#include "kitten.h"
#include "profile.hpp"

namespace CaDiCaL {

// This function determines the next decision variable on the queue, without
// actually removing it from the decision queue, e.g., calling it multiple
// times without any assignment will return the same result.  This is of
// course used below in 'decide' but also in 'reuse_trail' to determine the
// largest decision level to backtrack to during 'restart' without changing
// the assigned variables (if 'opts.restartreusetrail' is non-zero).

int Internal::next_decision_variable_on_queue () {
  int64_t searched = 0;
  int res = queue.unassigned;
  while (val (res))
    res = link (res).prev, searched++;
  if (searched) {
    stats.decision_searched += searched;
    update_queue_unassigned (res);
  }
  LOG ("next queue decision variable %d bumped %" PRId64 "", res,
       bumped (res));
  return res;
}

// This function determines the best decision with respect to score.
//
int Internal::next_decision_variable_with_best_score () {
  int res = 0;
  for (;;) {
    res = scores.front ();
    if (!val (res))
      break;
    (void) scores.pop_front ();
  }
  LOG ("next decision variable %d with score %g", res, score (res));
  return res;
}

void Internal::start_random_sequence () {
  if (!opts.randec)
    return;

  assert (!stable || opts.randecstable);
  assert (stable || opts.randecfocused);
  assert (!randomized_deciding);

  const uint64_t count = ++stats.decision_random_phase;
  const unsigned length = opts.randeclength * log (count + 10);
  VERBOSE (3,
           "starting random decision sequence "
           "at %" PRId64 " conflicts for %u conflicts",
           stats.conflicts, length);
  randomized_deciding = length;

  const double delta =
      stats.decision_random_phase * log (stats.decision_random_phase);
  lim.random_decision = stats.conflicts + delta * opts.randecint;
  VERBOSE (3,
           "next random decision sequence "
           "at %" PRId64 " conflicts current conflict: %" PRId64
           " conflicts",
           lim.random_decision, stats.conflicts);
}

int Internal::next_random_decision () {
  assert (max_var);
  if (!opts.randec)
    return 0;
  if (stable && !opts.randecstable)
    return 0;
  if (!stable && !opts.randecfocused)
    return 0;
  if (stats.conflicts < lim.random_decision)
    return 0;
  if (satisfied ())
    return 0;

  if (!randomized_deciding) {
    if (is_constraint_level (level)) {
      LOG ("random decision delayed because too deep");
      return 0;
    }
    start_random_sequence ();
  }
  LOG ("searching for random decision");
  Random random (internal->opts.seed);
  random += stats.decisions;
  ++stats.decision_random;
  for (;;) {
    int idx = 1 + (random.next () % max_var);
    LOG ("trying lit %s", LOGLIT (idx));
    /*
      // Kissat filters out active literals but we cannot do that because
      // eliminated variables are not actively removed.
    if (!flags (idx).active())
      continue;
    */
    if (val (idx))
      continue;
    if (flags (idx).unused ())
      continue;
    return idx;
  }
  assert (false);
  __builtin_unreachable ();
}

int Internal::next_decision_variable () {
  int res = next_random_decision ();
  if (res) {
    LOG ("randomized decision %s", LOGLIT (res));
    return res;
  }
  if (use_scores ())
    return next_decision_variable_with_best_score ();
  else
    return next_decision_variable_on_queue ();
}

/*------------------------------------------------------------------------*/

// Implements phase saving as well using a target phase during
// stabilization unless decision phase is forced to the initial value
// of a phase is forced through the 'phase' option.

int Internal::decide_phase (int idx, bool target) {
  const int initial_phase = opts.phase ? 1 : -1;
  int phase = 0;
  if (force_saved_phase) {
    phase = phases.saved[idx];
    LOG ("trying force_saved_phase, i.e., %d", phase);
  }
  assert (force_saved_phase || !phase);
  if (!phase) {
    phase = phases.forced[idx]; // swapped with opts.forcephase case!
    LOG ("trying forced phase, i.e., %d", phase);
  }
  if (!phase && opts.forcephase) {
    phase = initial_phase;
    LOG ("trying initial phase, i.e., %d", phase);
  }
  if (!phase && target) {
    phase = phases.target[idx];
  }
  if (!phase) {
    // ported from kissat where it does not seem very useful
    if (opts.stubbornIOfocused && opts.rephase == 2)
      switch ((stats.rephased >> 1) & 7) {
      case 1:
        phase = initial_phase;
        break;
      case 5: // kissat has 3 but 5 looks better
        phase = -initial_phase;
        break;
      default:
        phase = phases.saved[idx];
        break;
      }
    else
      phase = phases.saved[idx];
  }

  // The following should not be necessary and in some version we had even
  // a hard 'COVER' assertion here to check for this.   Unfortunately it
  // triggered for some users and we could not get to the root cause of
  // 'phase' still not being set here.  The logic for phase and target
  // saving is pretty complex, particularly in combination with local
  // search, and to avoid running in such an issue in the future again, we
  // now use this 'defensive' code here, even though such defensive code is
  // considered bad programming practice.
  //
  if (!phase)
    phase = initial_phase;

  return phase * idx;
}

// The likely phase of an variable used in 'collect' for optimizing
// co-location of clauses likely accessed together during search.

int Internal::likely_phase (int idx) { return decide_phase (idx, false); }

/*------------------------------------------------------------------------*/

// adds new level to control and trail
//
void Internal::new_trail_level (int lit) {
  level++;
  control.push_back (Level (lit, trail.size ()));
}

/*------------------------------------------------------------------------*/

bool Internal::satisfied () {
  check_var_stats ();
  LOG ("checking satisfied");
  if (is_constraint_level (level))
    return false;
  if (num_assigned + stats.vars_unused < (size_t) max_var)
    return false;
  assert (num_assigned + stats.vars_unused == (size_t) max_var);
  if (propagated < trail.size ())
    return false;
  size_t assigned = num_assigned;
  return (assigned + stats.vars_unused == (size_t) max_var);
}

bool Internal::better_decision (int lit, int other) {
  int lit_idx = abs (lit);
  int other_idx = abs (other);
  if (stable)
    return stab[lit_idx] > stab[other_idx];
  else
    return btab[lit_idx] > btab[other_idx];
}

#if defined(CHECKMISSED) && 1
#define CHECK_MISSED() \
  do { \
    for (auto *c : clauses) { \
      if (c->garbage) \
        continue; \
      bool SAT = false; \
      int PROP = 0; \
      for (auto &lit : *c) { \
        if (val (lit) > 0) { \
          SAT = true; \
          break; \
        } else if (val (lit) < 0) { \
          continue; \
        } else if (!PROP) { \
          PROP = lit; \
        } else { \
          PROP = 0; \
          break; \
        } \
      } \
      if (SAT || !PROP) \
        continue; \
      LOG (c, "fatal not propagated"); \
      assert (false); \
    } \
  } while (0)
#else
#define CHECK_MISSED() \
  do { \
  } while (0)
#endif

bool Internal::is_assumption_level (size_t level) {
  return level < assumptions.size ();
}
bool Internal::is_constraint_level (size_t level) {
  assert (constraints_without_assumptions <= constraint_vars.size ());
  if (constraint_cat &&
      KITTEN_NAMESPACE (kitten_status) (constraint_cat) == 11) {
    LOG ("level %zd < implicant %d?", level,
         KITTEN_NAMESPACE (kitten_size_implicant) (constraint_cat));
    return level <
           KITTEN_NAMESPACE (kitten_size_implicant) (constraint_cat);
  }
  LOG ("level %zd < assumptions %zd + constraints %zd?", level,
       assumptions.size (), constraints_without_assumptions);
  return level < assumptions.size () + constraints_without_assumptions;
}

int Internal::decide_assumption () {
  assert (is_assumption_level (level));
  int res = 0;
  if (constraint_cat) {
    int cat_res = KITTEN_NAMESPACE (kitten_status) (constraint_cat);
    if (!cat_res) {
      stats.constraints_solved++;
      if (!unit_constraint_vars && opts.constrainteager)
        eager_constraint_units ();
      PROFILE_SCOPE (constraintssolve);
      if (opts.constraintprime == 2)
        cat_res = KITTEN_NAMESPACE (kitten_solve_prime) (constraint_cat);
      else
        cat_res = KITTEN_NAMESPACE (kitten_solve) (constraint_cat);
      report ('a'); // TODO: maybe only verbose
      PROFILE_SCOPE_EARLY_EXIT (constraintssolve);
      if (cat_res == 20)
        stats.constraints_unsat++;
      else if (cat_res == 10)
        stats.constraints_sat++;
      else if (cat_res == 11)
        stats.constraints_prime++;
      else // kitten was terminated
        assert (terminated_asynchronously ());
    }
    if (cat_res == 20) { // unsat
      LOG ("constraints falsified");
      unsat_constraint = true;
      res = 20;
    }
  }
  if (!res && !terminated_asynchronously ()) {
    const int lit = assumptions[level];
    assert (assumed (lit));
    const signed char tmp = val (lit);
    if (tmp < 0) {
      LOG ("assumption %d falsified", lit);
      res = 20;
    } else if (tmp > 0) {
      LOG ("assumption %d already satisfied", lit);
      new_trail_level (0);
      LOG ("added pseudo decision level");
      notify_decision ();
    } else {
      LOG ("deciding assumption %d", lit);
      assert (!constraint_cat || KITTEN_NAMESPACE (kitten_signed_value) (
                                     constraint_cat, lit) > 0);
      search_assume_decision (lit);
    }
  }
  return res;
}

// check for falsified literals with respect to kitten trail
bool Internal::compute_diverged_constraint () {
  PROFILE_SCOPE (constraintsdiverge);
  assert (constraint_unsat.empty ());
  bool backtracked = false;
  for (auto &lit : constraint_vars) {
    const auto tmp_kit =
        KITTEN_NAMESPACE (kitten_signed_value) (constraint_cat, lit);
    const auto tmp_cad = val (lit);
    if (!tmp_cad)
      continue;
    if (tmp_kit == tmp_cad)
      continue;
    if (!tmp_kit && is_decision (lit)) {
      assert (KITTEN_NAMESPACE (kitten_status) (constraint_cat) == 11);
      LOG ("backtracking decision %d (not part of kitten implicant)", lit);
      backtrack (var (lit).level - 1);
      backtracked = true;
      continue;
    }
    if (!tmp_kit)
      continue;
    assert (tmp_kit);
    assert (tmp_kit == -tmp_cad);
    if (opts.constraintflip &&
        KITTEN_NAMESPACE (kitten_status) (constraint_cat) == 10 &&
        KITTEN_NAMESPACE (kitten_flip_signed_literal) (constraint_cat,
                                                       lit)) {
      stats.constraints_flipped++;
      continue;
    }
    constraint_unsat.push_back (lit);
  }
  if (constraint_unsat.empty ())
    return backtracked;
  int min = 0;
  for (auto &lit : constraint_unsat)
    if (!min || var (lit).level < var (min).level ||
        (var (lit).level == var (min).level &&
         var (lit).trail < var (min).trail))
      min = lit;
  if (!val (min)) {
    assert (backtracked);
  } else if (val (min) && is_decision (min)) {
    backtrack (var (min).level - 1);
  } else {
    assert (val (min) && level >= var (min).level);
    int failed = min;
    if (val (min) > 0)
      failed = -failed;
    analyze_failing_constraint (failed);
    // Kitten might fix the conflict by changing other parts of the
    // model so backtracking eagerly is not beneficial
    /*
    if (var (min).level)
      backtrack (var (min).level - 1);
      */
  }
  constraint_unsat.clear ();
  return true;
}

struct bigger_queue {

  Internal *internal;

  bigger_queue (Internal *i) : internal (i) {}

  bool operator() (int a, int b) {
    assert (a > 0), assert (abs (a) < internal->btab.size ());
    assert (b > 0), assert (abs (b) < internal->btab.size ());
    const unsigned s = internal->btab[a];
    const unsigned t = internal->btab[b];
    assert (s != t);
    return s > t;
  }
};

struct bigger_score {

  Internal *internal;

  bigger_score (Internal *i) : internal (i) {}

  bool operator() (int a, int b) {
    assert (a > 0), assert (abs (a) < internal->stab.size ());
    assert (b > 0), assert (abs (b) < internal->stab.size ());
    const unsigned s = internal->stab[a];
    const unsigned t = internal->stab[b];
    if (s == t)
      return a > b;
    return s > t;
  }
};

void Internal::eager_constraint_units () {
  unit_constraint_vars = true;
  for (auto &lit : constraint_vars) {
    const auto tmp = val (lit);
    if (tmp && !var (lit).level) {
      Flags &f = flags (lit);
      assert (f.constrained);
      if (!f.constrained_unit) {
        f.constrained_unit = true;
        const int64_t id = ++clause_id;
        assert (clause.empty ());
        if (proof) {
          clause.push_back (lit * tmp);
          if (lrat)
            lrat_chain.push_back (unit_id (lit * tmp));
          // not using constraints
          proof->add_assumption_clause (id, clause, lrat_chain, false);
          clause.clear ();
          lrat_chain.clear ();
        }
        KITTEN_NAMESPACE (cat_unit_with_id) (constraint_cat, id, lit * tmp);
      }
    }
  }
}
int Internal::decide_constraint () {
  assert (is_constraint_level (level));
  PROFILE_SCOPE (constraints);
  int cat_res = KITTEN_NAMESPACE (kitten_status) (constraint_cat);
  int res = 0;
  if (!cat_res) {
    // TODO: bump kitten (and sort before)
    // sort constraint_vars according to current decision heuristic
    if (opts.constraintsort) {
      stats.constraints_sorted++;
      if (use_scores ()) {
        LOG ("sorting constraint variables based on scores");
        sort (constraint_vars.begin (), constraint_vars.end (),
              bigger_score (this));
      } else {
        LOG ("sorting constraint variables based on queue idx");
        sort (constraint_vars.begin (), constraint_vars.end (),
              bigger_queue (this));
      }
      last_constraint_idx = 0;
    }
    if (opts.constraintbump == 2) {
      for (auto cv = constraint_vars.rbegin ();
           cv != constraint_vars.rend (); cv++) {
        KITTEN_NAMESPACE (kitten_bump_signed_literal (constraint_cat, *cv));
      }
    }
    if (!unit_constraint_vars && opts.constrainteager)
      eager_constraint_units ();
    stats.constraints_solved++;
    PROFILE_SCOPE (constraintssolve);
    if (opts.constraintprime == 2)
      cat_res = KITTEN_NAMESPACE (kitten_solve_prime) (constraint_cat);
    else
      cat_res = KITTEN_NAMESPACE (kitten_solve) (constraint_cat);
    report ('a'); // TODO: maybe only verbose
    PROFILE_SCOPE_EARLY_EXIT (constraintssolve);
    if (cat_res == 20)
      stats.constraints_unsat++;
    else if (cat_res == 10) {
      stats.constraints_sat++;
      if (opts.constraintprime == 1) {
        LOG ("computing kitten prime implicant");
        KITTEN_NAMESPACE (kitten_compute_prime_implicant) (constraint_cat);
        stats.constraints_prime++;
      }
      // compute conflicts between current trail and kitten model
      if (compute_diverged_constraint ()) {
        stats.constraints_diverged++;
        return 0;
      }
    } else if (cat_res == 11) {
      stats.constraints_prime++;
      // compute conflicts between current trail and kitten model
      if (compute_diverged_constraint ()) {
        stats.constraints_diverged++;
        return 0;
      }
    } else {
      // Kitten was terminated
      assert (terminated_asynchronously ());
      return 0;
    }
  }
  // assert (cat_res);
  if (terminated_asynchronously ())
    return 0;
  else if (!is_constraint_level (level))
    return 0;
  if (cat_res == 20) { // unsat
    LOG ("constraints falsified");
    unsat_constraint = true;
    res = 20;
  } else if (!cat_res)
    return 0;
  else {
    PROFILE_SCOPE (constraintsdecide)
    assert (cat_res == 10 || cat_res == 11);
    LOG ("using kitten model");
    bool all_constraints_assigned = true;
    // TODO: re-ordering based on decisions?
    // TODO: keep last constraint_var index to skip part of the loop.
    int lit = 0; //, last_lit;
    size_t idx = 0;
    assert (last_constraint_idx <= constraint_vars.size ());
    if (last_constraint_idx == constraint_vars.size ()) {
      if (control[level].decision == 0)
        idx = last_constraint_idx;
    } else {
      const int last_decision = constraint_vars[last_constraint_idx];
      // TODO: this is not precise due to fake-decisions
      if (val (last_decision) && var (last_decision).level == level &&
          is_decision (last_decision))
        idx = last_constraint_idx;
    }
    for (idx = 0; idx < constraint_vars.size (); idx++) {
      if (terminated_asynchronously ()) {
        all_constraints_assigned = false;
        break;
      }
      // last_lit = lit;
      lit = constraint_vars[idx];
      // constraint_vars[idx] = last_lit;
      const signed char tmp =
          KITTEN_NAMESPACE (kitten_signed_value) (constraint_cat, lit);
      // Ignore redundant variables.
      if (!tmp) {
        assert (KITTEN_NAMESPACE (kitten_status) (constraint_cat) == 11);
        continue;
      }
      assert (tmp);
      const signed char tmp_lit = val (lit);
      int decision = lit;
      if (tmp < 0)
        decision = -decision;
      if (!tmp_lit) {
        stats.constraints_decided++;
        assert (!flags (decision).unused ());
        search_assume_decision (decision);
        last_constraint_idx = idx;
        all_constraints_assigned = false;
        break;
      } else if (!tmp || tmp_lit == tmp) {
        LOG ("constraint literal %d already satisfied", lit);
        continue;
      } else if (opts.constraintflip &&
                 KITTEN_NAMESPACE (kitten_status) (constraint_cat) == 10 &&
                 KITTEN_NAMESPACE (kitten_flip_signed_literal) (
                     constraint_cat, lit)) {
        stats.constraints_flipped++;
      } else if (is_decision (lit)) {
        // happens if we have to recompute kitten model
        // TODO: should be caught by 'compute_diverged_constraint'
        assert (false);
        all_constraints_assigned = false;
        backtrack (var (lit).level - 1);
        break;
      } else {
        // this requires that the trail satisfies the current kitten
        // model, otherwise 'analyze_failing_constraint' might generate a
        // useless clause, leading to a potential infinite loop.
        assert (tmp_lit == -tmp);
        LOG ("constraint literal %d falsified", lit);
        int failed = lit;
        if (tmp_lit > 0)
          failed = -failed;
        analyze_failing_constraint (failed);
        // Kitten might fix the conflict by changing other parts of the
        // model so backtracking eagerly is not beneficial
        /*
        if (var (lit).level)
          backtrack (var (lit).level - 1);
          */
        all_constraints_assigned = false;
        PROFILE_SCOPE_EARLY_EXIT (constraintsdecide)
        break;
      }
      idx++;
    }
    /*
    assert (!constraint_vars[0]), assert (lit);
    constraint_vars[0] = lit;
    */
    if (all_constraints_assigned) {
      last_constraint_idx = constraint_vars.size ();
      stats.decisions++;
      LOG ("added pseudo decision level(s) due to constraints");
      new_trail_level (0);
      notify_decision ();
    }
  }
  return res;
}

// Search for the next decision and assign it to the saved phase. Requires
// that not all variables are assigned.

int Internal::decide () {
  assert (!satisfied ());
  PROFILE_SCOPE (decide);
  // during interaction with the user propagator, new variables can be added
  // (for example by observed).
  if (!imports.empty ())
    activating_all_new_imported_literals ();
  check_queue ();
  CHECK_MISSED ();
  int res = 0;
BEFORE: // UP force backtrack
  if (terminated_asynchronously ())
    return res;
  if (is_assumption_level (level)) {
    res = decide_assumption ();
  } else if (is_constraint_level (level)) {
    res = decide_constraint ();
  } else {
    check_queue ();
    int decision = ask_decision ();
    if (is_constraint_level (level)) {
      // Forced backtrack below pseudo decision levels.
      // So one of the two branches above will handle it.
      goto BEFORE;
    }
    stats.decisions++;
    if (!decision) {
      int idx = next_decision_variable ();
      const bool target = (opts.target > 1 || (stable && opts.target));
      decision = decide_phase (idx, target);
    }
    assert (!flags (decision).unused ());
    search_assume_decision (decision);
  }
  if (res)
    marked_failed = false;
  check_var_stats ();
  return res;
}
} // namespace CaDiCaL
