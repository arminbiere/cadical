#include "internal.hpp"
#include <algorithm>
#include <functional>

namespace CaDiCaL {

// It turns out that even in the competition there are formulas which are
// easy to satisfy by either setting all variables to the same truth value
// or by assigning variables to the same value and propagating it.  In the
// latter situation this can be done either in the order of all variables
// (forward or backward) or in the order of all clauses.  These lucky
// assignments can be tested initially in a kind of pre-solving step.

// We extended the search to do discrepency search to strengthen the
// original idea. We try both direction of a literal if it leads to a
// conflict. On top of that, as long as we are on level 1, we actually learn
// the unit, similarly to how probing is done.

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
  assert (propagated == trail.size ());
  if (conflict)
    conflict = nullptr;
  return res;
}

inline void Internal::lucky_search_assign (int lit, Clause *reason) {
  assert (searching_lucky_phases);
  if (level)
    MODE_REQUIRE (SEARCH);
  assert (!flags (lit).unused ());

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
    lit_level = level, reason = nullptr;
  else
    lit_level = level;
  if (!lit_level)
    reason = nullptr;

  v.level = lit_level;
  v.trail = get_trail_size ();
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
  MODE_REQUIRE (SEARCH);
  assert (propagated == trail.size ());
  new_trail_level (lit);
  LOG ("lucky decide %d", lit);
  lucky_search_assign (lit, decision_reason);
}

int Internal::trivially_false_satisfiable (int64_t &ticks) {
  if (terminated_asynchronously ())
    return -1;
  VERBOSE (3, "checking that all clauses contain a negative literal");
  assert (!level);
  ++stats.lucky_constant_zero;
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  ticks += 1 + cache_lines (clauses.size (), sizeof (clauses.begin ()));
  for (const auto &c : clauses) {
    ++ticks;
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
    if (flags (idx).unused ())
      continue;
    lucky_assume_decision (-idx);
    if (propagate ())
      continue;
    if (flags (idx).unused ())
      continue;
    assert (level > 0);
    LOG ("propagation failed including redundant clauses");
    return unlucky (0);
  }
  stats.lucky_constant_zero++;
  return 10;
}

int Internal::trivially_true_satisfiable (int64_t &ticks) {
  if (terminated_asynchronously ())
    return -1;
  VERBOSE (3, "checking that all clauses contain a positive literal");
  assert (!level);
  ++stats.lucky_constant_one;
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  ticks += 1 + cache_lines (clauses.size (), sizeof (clauses.begin ()));
  for (const auto &c : clauses) {
    ++ticks;
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
    if (flags (idx).unused ())
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

template <class Iterator>
int Internal::lucky_fixed_test (Iterator begin, Iterator end,
                                signed char pol, std::string str) {
  if (terminated_asynchronously ())
    return -1;
  VERBOSE (3, "checking %s variable index %s assignment", str.c_str (),
           pol == 1 ? "true" : "false");
#ifdef QUIET
  (void) str;
#endif
  assert (!unsat);
  assert (!level);
  if (pol == 1)
    stats.lucky_forward_one++;
  else
    stats.lucky_forward_zero++;
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (auto it = begin; it != end; ++it) {
    const int idx = *it;
    if (flags (idx).unused ())
      continue;
  START:
    int lit = idx * pol;
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    if (lucky_propagate_discrepency (lit)) {
      if (unsat)
        return 20;
      else
        return unlucky (0);
    } else
      goto START;
  }
  VERBOSE (1, "%s assuming variables %s satisfies formula", str.c_str (),
           pol == 1 ? "true" : "false");
  assert (satisfied ());
  return 10;
}

int Internal::forward_false_satisfiable () {
  return lucky_fixed_test (vars.begin (), vars.end (), -1, "forward");
}

int Internal::forward_true_satisfiable () {
  return lucky_fixed_test (vars.begin (), vars.end (), 1, "forward");
}

/*------------------------------------------------------------------------*/

int Internal::backward_false_satisfiable () {
  if (terminated_asynchronously ())
    return -1;
  VERBOSE (3, "checking decreasing variable index false assignment");
  assert (!unsat);
  assert (!level);
  stats.lucky_backward_zero++;
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (auto it = vars.rbegin (); it != vars.rend (); ++it) {
    int idx = *it;
    if (flags (idx).unused ())
      continue;
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
  if (terminated_asynchronously ())
    return -1;
  VERBOSE (3, "checking decreasing variable index true assignment");
  assert (!unsat);
  assert (!level);
  stats.lucky_backward_one++;
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (auto it = vars.rbegin (); it != vars.rend (); ++it) {
    int idx = *it;
    if (flags (idx).unused ())
      continue;
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

int Internal::lucky_decide_assumptions () {
  assert (!level);
  assert (!constraints.size ());
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

int Internal::random_lucky_assignment (signed char pol) {
  if (!opts.luckyrandom)
    return 0;
  VERBOSE (3, "checking random variable order %s assignment",
           pol == 1 ? "true" : "false");
  assert (!unsat);
  assert (!level);
  stats.lucky_random++;

  // Shuffle the variables
  std::vector<int> shuffle;
  for (int idx = max_var; idx; idx--) {
    if (val (idx))
      continue;
    if (flags (idx).unused ())
      continue;
    shuffle.push_back (idx);
  }
  Random random (opts.seed);    // global seed
  random += stats.lucky_random; // different every time
  const int highest_var = (int) shuffle.size ();
  for (int i = 0; i <= highest_var - 2; i++) {
    const int j = random.pick_int (i, highest_var - 1);
    swap (shuffle[i], shuffle[j]);
  }

  int res = lucky_decide_assumptions ();
  if (res)
    return res;

  for (int idx : shuffle) {
  START:
    if (flags (idx).unused ())
      continue;
    if (val (idx))
      continue;
    if (terminated_asynchronously (10))
      return unlucky (-1);

    int lit = idx * pol;
    if (lucky_propagate_discrepency (lit)) {
      if (unsat)
        return 20;
      else
        return unlucky (0);
    } else {
      goto START;
    }
  }
  VERBOSE (1, "random %s assignment satisfies formula",
           pol == 1 ? "true" : "false");
  assert (satisfied ());
  return 10;
}
/*------------------------------------------------------------------------*/

int Internal::lucky_phases (bool update_limit) {
  assert (!level);
  MODE_REQUIRE (SEARCH);
  if (!opts.lucky)
    return 0;

  if (!opts.luckyassumptions && !assumptions.empty ())
    return 0;
  if (terminated_asynchronously ())
    return 0;
  // TODO: Some of the lucky assignments can also be found if there are
  // constraint.
  if (!constraints.empty ())
    return 0;
  // External propagator assumes a CDCL loop, so lucky is not tried here.
  if (external_prop)
    return 0;
  if (unsat)
    return 20;
  if (!propagate ()) {
    learn_empty_clause ();
    return 20;
  }

  PROFILE_SCOPE2 (search, lucky);
  LOG ("starting lucky");
  assert (!searching_lucky_phases);
  searching_lucky_phases = true;
  stats.lucky_tried++;
  int64_t units = 0;
  int res = 0, rounds = 0;
#ifndef QUIET
  const int64_t active_initially = stats.vars_active;
#endif

  constexpr int schedule_size = 6;
  std::array<std::function<int ()>, schedule_size> schedule;
  int schedule_pos = 0;

  // The idea of the code is to:
  //
  //  1. check for the trival solutions. The trivial solution are
  // tested only once, because the forward/backward true/false would
  // solve the same model too (which higher cost).
  //
  // 2. a. use the order provided by the user (by default, the decisions are
  // largest first)
  //
  // b. then use first the phases proviveded by the user (by default '1')
  if (opts.phase) {
    if (!opts.varprioritizefirst) {
      schedule[schedule_pos++] = [this] () {
        return backward_true_satisfiable ();
      };
      schedule[schedule_pos++] = [this] () {
        return backward_false_satisfiable ();
      };
      schedule[schedule_pos++] = [this] () {
        return forward_true_satisfiable ();
      };
      schedule[schedule_pos++] = [this] () {
        return forward_false_satisfiable ();
      };
    } else {
      schedule[schedule_pos++] = [this] () {
        return forward_true_satisfiable ();
      };
      schedule[schedule_pos++] = [this] () {
        return forward_false_satisfiable ();
      };
      schedule[schedule_pos++] = [this] () {
        return backward_true_satisfiable ();
      };
      schedule[schedule_pos++] = [this] () {
        return backward_false_satisfiable ();
      };
    }
    schedule[schedule_pos++] = [this] () {
      return random_lucky_assignment (1);
    };
    schedule[schedule_pos++] = [this] () {
      return random_lucky_assignment (-1);
    };
  } else {
    if (!opts.varprioritizefirst) {
      schedule[schedule_pos++] = [this] () {
        return backward_false_satisfiable ();
      };
      schedule[schedule_pos++] = [this] () {
        return backward_true_satisfiable ();
      };
      schedule[schedule_pos++] = [this] () {
        return forward_false_satisfiable ();
      };
      schedule[schedule_pos++] = [this] () {
        return forward_true_satisfiable ();
      };
    } else {
      schedule[schedule_pos++] = [this] () {
        return forward_false_satisfiable ();
      };
      schedule[schedule_pos++] = [this] () {
        return forward_true_satisfiable ();
      };
      schedule[schedule_pos++] = [this] () {
        return backward_false_satisfiable ();
      };
      schedule[schedule_pos++] = [this] () {
        return backward_true_satisfiable ();
      };
    }
    schedule[schedule_pos++] = [this] () {
      return random_lucky_assignment (-1);
    };
    schedule[schedule_pos++] = [this] () {
      return random_lucky_assignment (1);
    };
  }
  assert (schedule_pos == schedule_size);

  if (res < 0)
    assert (termination_forced), res = 0;
  if (res == 10)
    stats.lucky++;
  report ('l', !res);
  assert (searching_lucky_phases);

  assert (res || !level);
  if (res != 20) {
    if (!propagate ()) {
      LOG ("propagating units after elimination results in empty clause");
      learn_empty_clause ();
    }
  }

  int64_t ticks = 0;
  res = trivially_false_satisfiable (ticks);
  if (!res)
    res = trivially_true_satisfiable (ticks);
  stats.ticks += ticks;

  const int64_t old_active = stats.vars_active;
  // abort the search if visit each clause too often
  const int64_t limit =
      stats.ticks + stats.clauses_now_irr * opts.luckylimitpercls;
  if (!res)
    do {
      const int64_t active_before = stats.vars_active;

      for (auto &luck : schedule) {
        res = luck ();
        if (res)
          break;
        if (stats.ticks >= limit)
          break;
      }
      if (res < 0)
        assert (termination_forced), res = 0;
      if (res == 10)
        stats.lucky++;
      assert (searching_lucky_phases);

      assert (res || !level);
      assert (res || propagated == trail.size ());

      units = active_before - stats.vars_active;
      stats.lucky_units += units;

      if (!res && units)
        VERBOSE (3, "lucky-%" PRId64 " in round %d found %" PRId64 " units",
                 stats.lucky_tried, rounds, units);
    } while (units && !res && ++rounds < opts.luckyrounds);

  report ('l', !res && (old_active == stats.vars_active));
  searching_lucky_phases = false;
  PHASE ("lucky", stats.lucky_tried,
         " produced %" PRId64 " units after %d rounds",
         active_initially - stats.vars_active, rounds);

  // Here we should reset lim.terminate.check since in a lucky run this
  // may be set to up to 1000 (for terminateint=10).
  // This then may lead to a high latency for external termination.
  lim.terminate.check = opts.terminateint;

  if (update_limit && !res && (old_active == stats.vars_active)) {
    lim.lucky = stats.conflicts + opts.luckymininterval;
    VERBOSE (
        3, "lucky-%" PRId64 " scheduled to be next after conflict %" PRId64,
        stats.lucky_tried, lim.lucky);
  }

  return res;
}

} // namespace CaDiCaL
