#include "internal.hpp"
#include <functional>

namespace CaDiCaL {

// It turns out that even in the competition there are formulas which are
// easy to satisfy by either setting all variables to the same truth value
// or by assigning variables to the same value and propagating it.  In the
// latter situation this can be done either in the order of all variables
// (forward or backward) or in the order of all clauses.  These lucky
// assignments can be tested initially in a kind of pre-solving step.

// We extended the search to do discrepency search to strengthen the original
// idea. We try both direction of a literal if it leads to a conflict. On top of
// that, as long as we are on level 1, we actually learn the unit, similarly to
// how probing is done.

// This function factors out clean up code common among the 'lucky'
// functions for backtracking and resetting a potential conflict.  One could
// also use exceptions here, but there are two different reasons for
// aborting early.  The first kind of aborting is due to asynchronous
// termination and the second kind due to a situation in which it is clear
// that a particular function will not be successful (for instance a
// completely negative clause is found).  The latter situation returns zero
// and will just abort the particular lucky function, while the former will
// abort all (by returning '-1').

int Internal::unlucky (int res) {
  if (level > 0)
    backtrack_without_updating_phases ();
  if (conflict)
    conflict = 0;
  return res;
}

inline void Internal::lucky_search_assign (int lit, Clause *reason) {
  assert (searching_lucky_phases);
  if (level)
    require_mode (SEARCH);

  const int idx = vidx (lit);
  assert (reason != external_reason);
  assert (!val (idx));
  assert (!flags (idx).eliminated () || reason == decision_reason ||
          reason == external_reason);
  Var &v = var (idx);
  int lit_level;
  assert (!lrat || level || reason == external_reason ||
          reason == decision_reason || !lrat_chain.empty ());
  // The following cases are explained in the two comments above before
  // 'decision_reason' and 'assignment_level'.
  //
  // External decision reason means that the propagation was done by
  // an external propagation and the reason clause not known (yet).
  // In that case it is assumed that the propagation is NOT out of
  // order (i.e. lit_level = level), because due to lazy explanation,
  // we can not calculate the real assignment level.
  // The function assignment_level () will also assign the current level
  // to literals with external reason.
  if (!reason)
    lit_level = 0; // unit
  else if (reason == decision_reason)
    lit_level = level, reason = 0;
  else
    lit_level = level;
  if (!lit_level)
    reason = 0;

  v.level = lit_level;
  v.trail = trail.size ();
  v.reason = reason;
  assert ((int) num_assigned < max_var);
  assert (num_assigned == trail.size ());
  num_assigned++;
  if (!lit_level)
    learn_unit_clause (lit); // increases 'stats.fixed'
  assert (lit_level);
  const signed char tmp = sign (lit);
  set_val (idx, tmp);
  assert (val (lit) > 0);  // Just a bit paranoid but useful.
  assert (val (-lit) < 0); // Ditto.
  trail.push_back (lit);
#ifdef LOGGING
  if (!lit_level)
    LOG ("root-level unit assign %d @ 0", lit);
  else
    LOG (reason, "search assign %d @ %d", lit, lit_level);
#endif

  if (watching ()) {
    const Watches &ws = watches (-lit);
    if (!ws.empty ()) {
      const Watch &w = ws[0];
      __builtin_prefetch (&w, 0, 1);
    }
  }
  lrat_chain.clear ();
}

void Internal::lucky_assume_decision (int lit) {
  require_mode (SEARCH);
  assert (propagated == trail.size ());
  new_trail_level (lit);
  LOG ("lucky decide %d", lit);
  lucky_search_assign (lit, decision_reason);
}

int Internal::trivially_false_satisfiable () {
  LOG ("checking that all clauses contain a negative literal");
  assert (!level);
  ++stats.lucky.constant.zero;
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (const auto &c : clauses) {
    if (terminated_asynchronously (100))
      return unlucky (-1);
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    bool satisfied = false, found_negative_literal = false;
    for (const auto &lit : *c) {
      const signed char tmp = val (lit);
      if (tmp > 0) {
        satisfied = true;
        break;
      }
      if (tmp < 0)
        continue;
      if (lit > 0)
        continue;
      found_negative_literal = true;
      break;
    }
    if (satisfied || found_negative_literal)
      continue;
    LOG (c, "found purely positively");
    return unlucky (0);
  }
  VERBOSE (1, "all clauses contain a negative literal");
  for (auto idx : vars) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    lucky_assume_decision (-idx);
    if (propagate ())
      continue;
    assert (level > 0);
    LOG ("propagation failed including redundant clauses");
    return unlucky (0);
  }
  stats.lucky.constant.zero++;
  return 10;
}

int Internal::trivially_true_satisfiable () {
  LOG ("checking that all clauses contain a positive literal");
  assert (!level);
  ++stats.lucky.constant.one;
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (const auto &c : clauses) {
    if (terminated_asynchronously (100))
      return unlucky (-1);
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    bool satisfied = false, found_positive_literal = false;
    for (const auto &lit : *c) {
      const signed char tmp = val (lit);
      if (tmp > 0) {
        satisfied = true;
        break;
      }
      if (tmp < 0)
        continue;
      if (lit < 0)
        continue;
      found_positive_literal = true;
      break;
    }
    if (satisfied || found_positive_literal)
      continue;
    LOG (c, "found purely negatively");
    return unlucky (0);
  }
  VERBOSE (1, "all clauses contain a positive literal");
  for (auto idx : vars) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    lucky_assume_decision (idx);
    if (propagate ())
      continue;
    assert (level > 0);
    LOG ("propagation failed including redundant clauses");
    return unlucky (0);
  }
  return 10;
}

/*------------------------------------------------------------------------*/
inline bool Internal::lucky_propagate_discrepency (int dec) {
  lucky_assume_decision (dec);
  bool no_conflict = propagate ();
  if (no_conflict)
    return false;
  if (level > 1) {
    conflict = nullptr;
    backtrack_without_updating_phases (level - 1);
    lucky_assume_decision (-dec);
    no_conflict = propagate ();
    if (no_conflict)
      return false;
    return true;
  } else {
    analyze ();
    assert (!level);
    no_conflict = propagate ();
    if (!no_conflict) {
      analyze ();
      LOG ("lucky inconsistency backward assigning to true");
      return true;
    }
  }
  return false;
}

int Internal::forward_false_satisfiable () {
  LOG ("checking increasing variable index false assignment");
  assert (!unsat);
  assert (!level);
  ++stats.lucky.forward.zero;
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (auto idx : vars) {
  START:
    if (terminated_asynchronously (100))
      return unlucky (-1);
    if (val (idx))
      continue;
    if (lucky_propagate_discrepency (-idx)) {
      if (unsat)
        return 20;
      else
        return unlucky (0);
    } else
      goto START;
  }
  VERBOSE (1, "forward assuming variables false satisfies formula");
  assert (satisfied ());
  return 10;
}

int Internal::forward_true_satisfiable () {
  LOG ("checking increasing variable index true assignment");
  assert (!unsat);
  assert (!level);
  stats.lucky.forward.one++;
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (auto idx : vars) {
  START:
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    if (lucky_propagate_discrepency (idx)) {
      if (unsat)
        return 20;
      else
        return unlucky (0);
    } else
      goto START;
  }
  VERBOSE (1, "forward assuming variables true satisfies formula");
  assert (satisfied ());
  return 10;
}

/*------------------------------------------------------------------------*/

int Internal::backward_false_satisfiable () {
  LOG ("checking decreasing variable index false assignment");
  assert (!unsat);
  assert (!level);
  stats.lucky.backward.zero++;
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (auto it = vars.rbegin (); it != vars.rend (); ++it) {
    int idx = *it;
  START:
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    if (lucky_propagate_discrepency (-idx)) {
      if (unsat)
        return 20;
      else
        return unlucky (0);
    } else
      goto START;
  }
  VERBOSE (1, "backward assuming variables false satisfies formula");
  assert (satisfied ());
  return 10;
}

int Internal::backward_true_satisfiable () {
  LOG ("checking decreasing variable index true assignment");
  assert (!unsat);
  assert (!level);
  stats.lucky.backward.one++;
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (auto it = vars.rbegin (); it != vars.rend (); ++it) {
    int idx = *it;
  START:
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    if (lucky_propagate_discrepency (idx)) {
      if (unsat)
        return 20;
      else
        return unlucky (0);
    } else
      goto START;
  }
  VERBOSE (1, "backward assuming variables true satisfies formula");
  assert (satisfied ());
  return 10;
}

/*------------------------------------------------------------------------*/

// The following two functions test if the formula is a satisfiable horn
// formula.  Actually the test is slightly more general.  It goes over all
// clauses and assigns the first positive literal to true and propagates.
// Already satisfied clauses are of course skipped.  A reverse function
// is not implemented yet.

int Internal::positive_horn_satisfiable () {
  LOG ("checking that all clauses are positive horn satisfiable");
  assert (!level);
  stats.lucky.horn.positive++;
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (const auto &c : clauses) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    int positive_literal = 0;
    bool satisfied = false;
    for (const auto &lit : *c) {
      const signed char tmp = val (lit);
      if (tmp > 0) {
        satisfied = true;
        break;
      }
      if (tmp < 0)
        continue;
      if (lit < 0)
        continue;
      positive_literal = lit;
      break;
    }
    if (satisfied)
      continue;
    if (!positive_literal) {
      LOG (c, "no positive unassigned literal in");
      return unlucky (0);
    }
    assert (positive_literal > 0);
    LOG (c, "found positive literal %d in", positive_literal);
    lucky_assume_decision (positive_literal);
    if (propagate ())
      continue;
    LOG ("propagation of positive literal %d leads to conflict",
         positive_literal);
    return unlucky (0);
  }
  for (auto idx : vars) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    lucky_assume_decision (-idx);
    if (propagate ())
      continue;
    LOG ("propagation of remaining literal %d leads to conflict", -idx);
    return unlucky (0);
  }
  VERBOSE (1, "clauses are positive horn satisfied");
  assert (!conflict);
  assert (satisfied ());
  return 10;
}

int Internal::lucky_decide_assumptions () {
  assert (!level);
  assert (!constraint.size ());
  int res = 0;
  while ((size_t) level < assumptions.size ()) {
    res = decide ();
    if (res == 20) {
      marked_failed = false;
      return 20;
    }
    if (!propagate ()) {
      break;
    }
  }

  if (conflict) {
    // analyze and learn from the conflict.
    LOG (conflict, "setting assumption lead to conflict");
    analyze_wrapper ();
    backtrack_without_updating_phases (0);
    assert (!conflict);
    int res = 0;
    while (!res) {
      assert ((size_t) level <= assumptions.size ());
      if (unsat)
        res = 20;
      else if (!propagate ()) {
        analyze_wrapper ();
      } else {
        res = decide_wrapper ();
      }
    }
    assert (res == 20);
    return 20;
  }
  return 0;
}

int Internal::negative_horn_satisfiable () {
  assert (!level);
  LOG ("checking that all clauses are negative horn satisfiable");
  stats.lucky.horn.negative++;
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (const auto &c : clauses) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    int negative_literal = 0;
    bool satisfied = false;
    for (const auto &lit : *c) {
      const signed char tmp = val (lit);
      if (tmp > 0) {
        satisfied = true;
        break;
      }
      if (tmp < 0)
        continue;
      if (lit > 0)
        continue;
      negative_literal = lit;
      break;
    }
    if (satisfied)
      continue;
    if (!negative_literal) {
      if (level > 0)
        backtrack_without_updating_phases ();
      LOG (c, "no negative unassigned literal in");
      return unlucky (0);
    }
    assert (negative_literal < 0);
    LOG (c, "found negative literal %d in", negative_literal);
    lucky_assume_decision (negative_literal);
    if (propagate ())
      continue;
    LOG ("propagation of negative literal %d leads to conflict",
         negative_literal);
    return unlucky (0);
  }
  for (auto idx : vars) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    lucky_assume_decision (idx);
    if (propagate ())
      continue;
    LOG ("propagation of remaining literal %d leads to conflict", idx);
    return unlucky (0);
  }
  VERBOSE (1, "clauses are negative horn satisfied");
  assert (!conflict);
  assert (satisfied ());
  return 10;
}

/*------------------------------------------------------------------------*/

int Internal::lucky_phases () {
  assert (!level);
  require_mode (SEARCH);
  if (!opts.lucky)
    return 0;

  if (!opts.luckyassumptions && !assumptions.empty ())
    return 0;
  // TODO: Some of the lucky assignments can also be found if there are
  // constraint.
  // External propagator assumes a CDCL loop, so lucky is not tried here.
  if (!constraint.empty () || external_prop)
    return 0;
  if (unsat)
    return 20;
  if (!propagate ()) {
    learn_empty_clause ();
    return 20;
  }

  START (search);
  START (lucky);
  LOG ("starting lucky");
  assert (!searching_lucky_phases);
  searching_lucky_phases = true;
  stats.lucky.tried++;
  int64_t units =0;
  int res = 0, rounds = 0;
  const int64_t active_initially = stats.active;

  std::vector<std::function<int ()> > schedule;
  schedule.reserve (8);

  // The idea of the code is to:
  // 1. check for the trival solutions
  //
  // 2. a. use the order provided by the user (by default, the decisions are
  // largest first)
  //
  // b. then use first the phases proviveded by the user (by default '1')
  if (opts.phase) {
    schedule.push_back([this]() {return trivially_true_satisfiable();});
    schedule.push_back([this]() {return trivially_false_satisfiable();});

    if (!opts.reverse) {
      schedule.push_back([this]() {return backward_true_satisfiable();});
      schedule.push_back([this]() {return backward_false_satisfiable();});
      schedule.push_back([this]() {return forward_true_satisfiable();});
      schedule.push_back([this]() {return forward_false_satisfiable();});
    } else {
      schedule.push_back([this]() {return forward_true_satisfiable();});
      schedule.push_back([this]() {return forward_false_satisfiable();});
      schedule.push_back([this]() {return backward_true_satisfiable();});
      schedule.push_back([this]() {return backward_false_satisfiable();});
    }

    schedule.push_back([this]() {return positive_horn_satisfiable();});
    schedule.push_back([this]() {return negative_horn_satisfiable();});
  } else {
    schedule.push_back([this]() {return trivially_true_satisfiable();});
    schedule.push_back([this]() {return trivially_false_satisfiable();});

    if (!opts.reverse) {
      schedule.push_back([this]() {return backward_false_satisfiable();});
      schedule.push_back([this]() {return backward_true_satisfiable();});
      schedule.push_back([this]() {return forward_false_satisfiable();});
      schedule.push_back([this]() {return forward_true_satisfiable();});
    } else {
      schedule.push_back([this]() {return forward_false_satisfiable();});
      schedule.push_back([this]() {return forward_true_satisfiable();});
      schedule.push_back([this]() {return backward_false_satisfiable();});
      schedule.push_back([this]() {return backward_true_satisfiable();});
    }
    schedule.push_back([this]() {return negative_horn_satisfiable();});
    schedule.push_back([this]() {return positive_horn_satisfiable();});
  }

  do {
    const int64_t active_before = stats.active;

    for (auto &luck : schedule) {
      res = luck ();
      if (res)
        break;
    }
    if (res < 0)
      assert (termination_forced), res = 0;
    if (res == 10)
      stats.lucky.succeeded++;
    assert (searching_lucky_phases);

    assert (res || !level);
    if (res != 20) {
      if (!propagate ()) {
        LOG ("propagating units after elimination results in empty clause");
        learn_empty_clause ();
      }
    }

    units = active_before - stats.active;
    stats.lucky.units += units;

    if (!res && units)
      PHASE ("lucky", stats.lucky.tried, "in round %d found %" PRId64 " units", rounds, units);
  } while (units && !res && ++rounds < opts.luckyrounds);

  report ('l', !res && !units);
  searching_lucky_phases = false;
  PHASE ("lucky", stats.lucky.tried, "produced %" PRId64 " units after %d rounds", active_initially - stats.active, rounds);

  STOP (lucky);
  STOP (search);

  return res;
}

} // namespace CaDiCaL
