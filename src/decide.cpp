#include "internal.hpp"

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
    stats.searched += searched;
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

int Internal::next_decision_variable () {
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
  if (force_saved_phase)
    phase = phases.saved[idx];
  if (!phase)
    phase = phases.forced[idx]; // swapped with opts.forcephase case!
  if (!phase && opts.forcephase)
    phase = initial_phase;
  if (!phase && target)
    phase = phases.target[idx];
  if (!phase)
    phase = phases.saved[idx];

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
  assert (assumptions2.satisfied ());
  assert (assumptions2.satisfied ());
  assert (!constraining());
  for (auto lit : assumptions2) {
    assert (val (lit) > 0);
  }
  if (constraining ()) // should be removed in the CDCL loop... the optimizer can do that
    return false;
  if (num_assigned < (size_t) max_var)
    return false;
  assert (num_assigned == (size_t) max_var);
  if (propagated < trail.size ())
    return false;
  size_t assigned = num_assigned;
  return (assigned == (size_t) max_var);
}

bool Internal::better_decision (int lit, int other) {
  int lit_idx = abs (lit);
  int other_idx = abs (other);
  if (stable)
    return stab[lit_idx] > stab[other_idx];
  else
    return btab[lit_idx] > btab[other_idx];
}

// Search for the next decision and assign it to the saved phase.  Requires
// that not all variables are assigned.

int Internal::decide () {
  assert (!satisfied ());
  START (decide);
  int res = 0;
  int lit = 0;
  assert (assumptions2.satisfied ());
  assert (!constraining ());

  if (false && constraining())
    res = decide_constrain();
  else {
  assert (!lit);
  LOG ("now real decision");
  stats.decisions++;
  int decision = ask_decision ();
  if (!decision) {
    int idx = next_decision_variable ();
    const bool target = (opts.target > 1 || (stable && opts.target));
    decision = decide_phase (idx, target);
  }
  search_assume_decision (decision);
  }
  if (res)
    marked_failed = false;
  STOP (decide);
  return res;
}

int Internal::decide_assumption() {
  int res = 0;
  int lit = assumptions2.next ();
  const signed char tmp = val (lit);
  if (tmp < 0) {
    LOG ("assumption %d falsified", lit);
    res = 20;
    marked_failed = false;
  } else if (tmp > 0) {
    LOG ("assumption %d already satisfied", lit);
    lit = 0;
  } else {
    LOG ("deciding assumption %d", lit);
    assumptions2.decide ();
    search_assume_decision (lit);
  }
  return res;  
}

} // namespace CaDiCaL
