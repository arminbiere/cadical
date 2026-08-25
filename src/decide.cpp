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
  return level < assumptions.size () + constraints_without_assumptions;
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
  // TODO: refactor this part
  if (is_assumption_level (level) && constraint_cat) {
    int cat_res = KITTEN_NAMESPACE (kitten_status (constraint_cat));
    if (!cat_res) {
      stats.constraints_solved++;
      PROFILE_SCOPE (constraintssolve);
      cat_res = KITTEN_NAMESPACE (kitten_solve (constraint_cat));
      PROFILE_SCOPE_EARLY_EXIT (constraintssolve);
      if (cat_res == 20)
        stats.constraints_unsat++;
      else if (cat_res == 10)
        stats.constraints_sat++;
      else {
        // Kitten was terminated
        assert (terminated_asynchronously ());
      }
    }
    if (cat_res == 20) { // unsat
      LOG ("constraints falsified");
      unsat_constraint = true;
      res = 20;
    }
    if (cat_res == 10) {
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
        search_assume_decision (lit);
      }
    }
  } else if (is_assumption_level (level)) {
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
      search_assume_decision (lit);
    }
  } else if (is_constraint_level (level)) {
    PROFILE_SCOPE (constraints);
    int cat_res = KITTEN_NAMESPACE (kitten_status (constraint_cat));
    if (!cat_res) {
      stats.constraints_solved++;
      PROFILE_SCOPE (constraintssolve);
      cat_res = KITTEN_NAMESPACE (kitten_solve (constraint_cat));
      PROFILE_SCOPE_EARLY_EXIT (constraintssolve);
      if (cat_res == 20)
        stats.constraints_unsat++;
      else if (cat_res == 10)
        stats.constraints_sat++;
      else {
        // Kitten was terminated
        assert (terminated_asynchronously ());
      }
    }
    // assert (cat_res);
    if (cat_res == 20) { // unsat
      LOG ("constraints falsified");
      unsat_constraint = true;
      res = 20;
    } else if (cat_res == 10) {
      LOG ("using kitten model");
      bool all_constraints_assigned = true;
      for (auto &lit : constraint_vars) {
        const signed char tmp =
            KITTEN_NAMESPACE (kitten_signed_value (constraint_cat, lit));
        assert (tmp);
        const signed char tmp_lit = val (lit);
        int decision = lit;
        if (tmp < 0)
          decision = -decision;
        if (!tmp_lit) {
          stats.decisions++;
          assert (!flags (decision).unused ());
          search_assume_decision (decision);
          all_constraints_assigned = false;
          break;
        } else if (tmp_lit == tmp) {
          LOG ("constraint literal %d already satisfied", lit);
          continue;
        } else if (is_decision (lit)) {
          // happens if we have to recompute kitten model
          // assert (false);
          all_constraints_assigned = false;
          backtrack (var (lit).level - 1);
          break;
        } else if (KITTEN_NAMESPACE (
                       kitten_flip_signed_literal (constraint_cat, lit))) {
          stats.constraints_flipped++;
        } else {
          assert (tmp_lit == -tmp);
          LOG ("constraint literal %d falsified", lit);
          int failed = lit;
          if (tmp_lit > 0)
            failed = -failed;
          analyze_failing_constraint (failed);
          if (var (lit).level)
            backtrack (var (lit).level - 1);
          all_constraints_assigned = false;
          break;
        }
      }
      if (all_constraints_assigned) {
        stats.decisions++;
        LOG ("added pseudo decision level(s) due to constraints");
        new_trail_level (0);
        notify_decision ();
      }
    }
    PROFILE_SCOPE_EARLY_EXIT (constraints);
  } else {
    check_queue ();
    int decision = ask_decision ();
    if (is_constraint_level (level)) {
      // Forced backtrack below pseudo decision levels.
      // So one of the two branches above will handle it.
      return decide ();
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
