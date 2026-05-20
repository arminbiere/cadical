#include "internal.hpp"

#include <algorithm>

namespace CaDiCaL {

#ifndef NTRACING
#define LOG_INTERACTION_START(NAME) LOG (#NAME " on level %d START", level);
#define LOG_INTERACTION_FOR(NAME, VAL) \
  LOG (#NAME "(%d) on level %d START", VAL, level)

static void trace_api_call (FILE *trace_api_file, Internal *internal,
                            const char *s0) {
  assert (trace_api_file);
  LOG ("TRACE %s", s0);
  (void) internal;
  fprintf (trace_api_file, "%s\n", s0);
  fflush (trace_api_file);
}
static void trace_api_call (FILE *trace_api_file, Internal *internal,
                            const char *s0, int i1) {
  assert (trace_api_file);
  LOG ("TRACE %s %d", s0, i1);
  (void) internal;
  fprintf (trace_api_file, "%s %d\n", s0, i1);
  fflush (trace_api_file);
}
static void trace_api_call (FILE *trace_api_file, Internal *internal,
                            const char *s0, int i1, int i2) {
  assert (trace_api_file);
  LOG ("TRACE %s %d", s0, i1);
  (void) internal;
  fprintf (trace_api_file, "%s %d %d\n", s0, i1, i2);
  fflush (trace_api_file);
}

#define LOG_INTERACTION_END(NAME) \
  do { \
    LOG (#NAME " on level %d END", level); \
    if (!external->trace_api_file) \
      break; \
    trace_api_call (external->trace_api_file, this, #NAME); \
  } while (0)
#define LOG_INTERACTION_RETURN(NAME, VAL) \
  do { \
    LOG (#NAME " returns %d on level %d END", VAL, level); \
    if (!external->trace_api_file) \
      break; \
    trace_api_call (external->trace_api_file, this, #NAME, VAL); \
  } while (0)
#define LOG_INTERACTION_RETURN_FOR(NAME, VAL, RET) \
  do { \
    LOG (#NAME "(%d) returns %d on level %d END", VAL, RET, level); \
    if (!external->trace_api_file) \
      break; \
    trace_api_call (external->trace_api_file, this, #NAME, VAL, RET); \
  } while (0)
#define LOG_INTERACTION_END_FOR(NAME, VAL) \
  do { \
    LOG (#NAME "(%d) on level %d END", VAL, level); \
    if (!external->trace_api_file) \
      break; \
    trace_api_call (external->trace_api_file, this, #NAME, VAL); \
  } while (0)
#else
#define LOG_INTERACTION_START(NAME) LOG (#NAME " on level %d START", level)
#define LOG_INTERACTION_FOR(NAME, VAL) \
  LOG (#NAME "(%d) on level %d START", VAL, level)

#define LOG_INTERACTION_END(NAME) LOG (#NAME " on level %d END", level)
#define LOG_INTERACTION_RETURN(NAME, VAL) \
  LOG (#NAME "returns %d on level %d END", VAL, level)
#define LOG_INTERACTION_END_FOR(NAME) \
  LOG (#NAME "(%d) on level %d END", VAL, level)
#define LOG_INTERACTION_RETURN_FOR(NAME, VAL, RET) \
  LOG (#NAME "(%d) returns %d on level %d END", VAL, RET, level)
#endif

/*----------------------------------------------------------------------------*/
//
// Mark a variable as an observed one. It can be a new variable. It is
// assumed to be clean (not eliminated by previous simplifications).
//
void Internal::add_observed_var (int ilit) {
  int idx = vidx (ilit);
  if (idx >= (int64_t) relevanttab.size ())
    relevanttab.resize (1 + (size_t) idx, 0);
  unsigned &ref = relevanttab[idx];
  if (flags (idx).unused ())
    declare_variable (idx);
  if (ref < UINT_MAX) {
    ref++;
    LOG ("variable %d is observed %u times", idx, ref);
  } else
    LOG ("variable %d remains observed forever", idx);
  // TODO: instead of actually backtracking, it would be enough to notify
  // backtrack and re-play again every levels' notification to the
  // propagator
  if (val (ilit) && level && !fixed (ilit)) {
    assert (!force_no_backtrack);
    // The variable is already assigned, but we can not send a notification
    // about it because it happened on an earlier decision level.
    // To not break the stack-like view of the trail, we simply backtrack to
    // undo this unnotifiable assignment.
    const int assignment_level = var (ilit).level;
    backtrack_without_updating_phases (assignment_level - 1);
  } else if (level && fixed (ilit)) {
    assert (!force_no_backtrack);
    backtrack_without_updating_phases (0);
  }
  activating_all_new_imported_literals ();
}

/*----------------------------------------------------------------------------*/
//
// Removing an observed variable should happen only once it is ensured
// that there is no unexplained propagation in the implication
// graph involving this variable. To ensure that, the solver might
// need to backtrack so that the variable becomes unassigned.
//
void Internal::remove_observed_var (int ilit) {
  if (!fixed (ilit) && level && val (ilit)) {
    const int assignment_level = var (ilit).level;
    backtrack_without_updating_phases (assignment_level - 1);
  }

  assert (fixed (ilit) || !val (ilit));

  const int idx = vidx (ilit);
  assert ((size_t) idx < relevanttab.size ());
  unsigned &ref = relevanttab[idx];
  assert (fixed (ilit) || ref > 0);
  if (fixed (ilit))
    ref = 0;
  else if (ref < UINT_MAX) {
    if (!--ref) {
      LOG ("variable %d is not observed anymore", idx);
    } else
      LOG ("variable %d is unobserved once but remains observed %u times",
           ilit, ref);
  } else
    LOG ("variable %d remains observed forever", idx);
}

/*----------------------------------------------------------------------------*/
//
// Supposed to be used only by mobical.
//
bool Internal::observed (int ilit) const {
  assert ((size_t) vidx (ilit) < relevanttab.size ());
  return relevanttab[vidx (ilit)] > 0;
}

/*----------------------------------------------------------------------------*/
//
// Check for unexplained propagations upon disconnecting external propagator
//
void Internal::set_changed_val () {
  if (!opts.ilb) {
    return;
  }
  for (auto idx : vars) {
    if (!val (idx))
      continue;
    if (var (idx).reason != external_reason)
      continue;
    if (!earliest_changed_val) {
      earliest_changed_val = idx;
      continue;
    }
    assert (val (earliest_changed_val));
    if (var (idx).level < var (earliest_changed_val).level) {
      earliest_changed_val = idx;
    }
  }
}

/*----------------------------------------------------------------------------*/
//
// Check if the variable is assigned by decision.
//
bool Internal::is_decision (int ilit) {
  if (!level || fixed (ilit) || !val (ilit))
    return false;

  const int idx = vidx (ilit);
  Var &v = var (idx);
#ifndef NDEBUG
  LOG (v.reason,
       "is_decision: i%d (current level: %d, is_fixed: %d, v.level: %d, "
       "is_external_reason: %d, v.reason: )",
       ilit, level, fixed (ilit), v.level, v.reason == external_reason);
#endif
  if (!v.level || v.reason)
    return false;
  assert (!v.reason);
  return true;
}

void Internal::force_backtrack (int new_level) {

  LOG ("external propagator forces backtrack to decision level"
       " %d (from level %d)",
       new_level, level);
  backtrack (new_level);
}

/*----------------------------------------------------------------------------*/
//
// Call external propagator to check if there is a literal to be propagated.
// The reason of the propagation is not necessarily asked at that point.
//
// In case the externally propagated literal is already falsified, the
// reason is asked and conflict analysis starts. In case the externally
// propagated literal is already satisfied, nothing happens.
//
bool Internal::external_propagate () {
  if (!external_prop || external_prop_is_lazy) {
    return false;
  }
  // if (level)
  require_mode (SEARCH);
  LOG ("external propagation starts (decision level: %d, trail size: "
       "%zd, notified %zd)",
       level, trail.size (), notified_trail);

  while (true) {
    assert (notified_trail == trail.size ());
    assert (notified_level == level);
    assert (!unsat);
    assert (!conflict);

    // external->reset_extended (); //TODO for inprocessing

    stats.up_cb++;
    stats.up_cb_prop++;
    LOG_INTERACTION_START (cb_propagate);
    const int elit = external->propagator->cb_propagate ();
    LOG_INTERACTION_RETURN (cb_propagate, elit);

    if (level < notified_level || notified_trail < trail.size ()) {
      LOG ("cb_propagate triggered a backtrack, ignoring return value %d",
           elit);
      return true;
    }
    if (!elit)
      break;

    if (!external->observed (elit))
      FATAL ("external propagations are only allowed over observed "
             "variables.");

    assert (external->is_observed[abs (elit)]);
    // TODO: double-check side-effects of internalize
    int ilit = external->internalize (elit);
    int tmp = val (ilit);
    LOG ("External propagation of e%d (i%d val: %d)", elit, ilit, tmp);

    if (tmp > 0) {
      // TODO: make this FATAL ?
      LOG ("ignoring external propagation on satisfied %s.", LOGLIT (ilit));
      continue;
    }
    if (tmp < 0) {
      assert (fixed (ilit) || observed (ilit));
      LOG ("External propgation of %s is falsified under current trail",
           LOGLIT (ilit));
      stats.up_cb_prop_clash++;
      Clause *res = learn_external_reason_clause (ilit, elit);
      LOG (res, "reason clause of external propagation of %d:", elit);
      (void) res;

      // This assertion, while technically still true does not
      // hold if the user is notified of the backtrack during
      // learn_external_reason_clause.
      // assert (unsat || conflict || level < notified_level);
      return true;
    }

    // variable is not assigned, it can be propagated
    assert (observed (ilit));

    stats.up_cb_prop_assign++;
    if (!level) {
      stats.up_cb_prop_unit++;
      Clause *res = learn_external_reason_clause (ilit, elit);
      LOG (res, "reason clause of external propagation of %d:", elit);
      (void) res;
    } else
      search_assign_external (ilit);
    assert (level == notified_level);
    assert (!unsat && !conflict);

    propagate ();

    assert (level == notified_level);
    if (unsat || conflict)
      return true;

    // user can interact here again.
    if (notifying_assignments ())
      return true;
  }
  LOG ("external_propagation ends without backtracking or conflict");
  // reached when user returns 0 on cb_propagate and levels did not change.
  return false;
}

// similar to external_propagate but with clause adding.
bool Internal::external_adding_clauses () {
  if (!external_prop || external_prop_is_lazy) {
    return false;
  }
  assert (notified_trail == trail.size ());
  assert (notified_level == level);
  assert (!unsat);
  assert (!conflict);
  bool added = false;
  while (true) {
    LOG ("external clause adding starts (decision level: %d, trail size: "
         "%zd, notified %zd)",
         level, trail.size (), notified_trail);

    stats.up_cb++;
    stats.up_cb_asked++;
    // do you want to add a clause
    const bool adding = ask_external_clause ();

    if (!adding)
      break;
    added = true;
    stats.up_cb_asked_added++;

    // actually adding the clause
    add_external_clause ();

    if (!unsat)
      propagate ();
    if (conflict || unsat) {
      LOG ("external clause addition lead to conflict");
      return true;
    }
  }
  if (level < notified_level) {
    LOG ("external clause addition changed level");
    return true;
  }
  assert (level == notified_level);
  if (!propagate ()) {
    LOG ("external clause addition lead to conflict");
    return true;
  }
  assert (!conflict && !unsat);
  // Only necessary when clause addition returns false but
  // there are new assignments.
  // notifying_assignments ();
  if (added) {
    LOG ("external clause addition added clauses");
    return true;
  }
  assert (notified_trail == trail.size ());
  LOG ("external clause addition did not add clauses");
  return false;
}

/*----------------------------------------------------------------------------*/
//
// Helper function, calls 'cb_has_external_clause', while maintains the
// related redundancy type of the clause.
//

bool Internal::ask_external_clause () {
  ext_clause_forgettable = false;
  LOG_INTERACTION_START (cb_has_external_clause);
  bool res =
      external->propagator->cb_has_external_clause (ext_clause_forgettable);
  LOG_INTERACTION_RETURN (cb_has_external_clause, res);

  return res;
}
/*----------------------------------------------------------------------------*/
//
// Literals of the externally learned clause must be reordered based on
// the assignment levels of the literals. Returns the best clause idx
// (except ignore)
size_t Internal::best_literal_to_watch (int ignore, bool trail_over_level) {
  size_t lit_position = 0;
  int lit = 0;

  int lit_level = 0;
  signed char lit_value = 0;
  int lit_trail = 0;
  for (size_t i = 0; i < clause.size (); i++) {

    const int other = clause[i];
    if (other == ignore)
      continue;
    assert (other);

    const int other_level = var (other).level;
    const signed char other_value = val (other);
    const int other_trail = var (other).trail;

    if (!lit ||                                         // no candidate yet.
        lit_value < other_value ||                      // -1 < 0 < 1
        (lit_value == other_value &&                    // Tie breaker:
         ((lit_value < 0 &&                             // -1:
           ((!trail_over_level &&                       // level over trail:
             (lit_level < other_level ||                // higher level, or
              (lit_level == other_level &&              // equal level:
               lit_trail < other_trail))) ||            // higher trail
            (trail_over_level &&                        // trail over level:
             lit_trail < other_trail))) ||              // higher trail
          (lit_value > 0 && lit_level > other_level)))) // 1: lower level
    {
      lit = other;
      lit_position = i;
      lit_value = other_value;
      lit_level = other_level;
      lit_trail = other_trail;
    }
  }
  assert (lit);
  return lit_position;
}

void Internal::move_literals_to_watch () {
  if (clause.size () < 2)
    return;
  if (!level)
    return;

  size_t best1 = best_literal_to_watch (0, false);
  const int lit = clause[best1];
  if (best1 != 0)
    std::swap (clause[0], clause[best1]);

  size_t best2 = best_literal_to_watch (lit, false);
  // const int other = clause[best2];

  assert (best2 && clause[best2] != lit);

  if (best2 != 1)
    std::swap (clause[1], clause[best2]);
}

/*----------------------------------------------------------------------------*/
//
// Reads out from the external propagator the lemma/proapgation reason
// clause literal by literal. In case prop_elit is 0, it is about an
// external clause via 'cb_add_external_clause_lit'. Otherwise, it is
// about learning the reason of 'prop_elit' via
// 'cb_add_reason_clause_lit'. The learned clause is simplified by the
// current root-level assignment (i.e. root-level falsified literals are
// removed, root satisfied clauses are skipped). Duplicate literals are
// removed, tauotologies are detected and skipped. It always adds the
// original (un-simplified) external clause to the proof as an input
// clause and the simplified version of it (except exceptions below) as a
// derived clause.
//
// In case the external clause, after simplifications, is satisfied, no
// clause is constructed, and the function returns 0. In case the external
// clause, after simplifications, is empty, no clause is constructed,
// unsat is set true and the function returns 0. In case the external
// clause, after simplifications, is unit, no clause is constructed,
// 'Internal::clause' has the unit literal (without 0) and the function
// returns 0.
//
// In every other cases a new clause is constructed and the pointer is in
// newest_clause
//
void Internal::add_external_clause (int prop_elit) {
  assert (!from_propagator);

  int elit = 0;
  bool propagated_lit_found = false;

  assert (tmp_elits.empty ());

  stats.up_cb_add++;
  while (true) {
    if (prop_elit) {
      stats.up_cb_add_reason++;
      LOG_INTERACTION_FOR (cb_add_reason_clause_lit, prop_elit);
      elit = external->propagator->cb_add_reason_clause_lit (prop_elit);
      LOG_INTERACTION_RETURN_FOR (cb_add_reason_clause_lit, prop_elit,
                                  elit);
    } else {
      stats.up_cb_add_external++;
      LOG_INTERACTION_START (cb_add_external_clause_lit);
      elit = external->propagator->cb_add_external_clause_lit ();
      LOG_INTERACTION_RETURN (cb_add_external_clause_lit, elit);
    }
    LOG ("cb_add %d", elit);

    tmp_elits.push_back (elit);

    if (!elit)
      break;

    if (elit == prop_elit)
      propagated_lit_found = true;

    if (!external->observed (elit))
      FATAL ("external clause must contain only observed variables.");
    if (prop_elit && elit != prop_elit && external->current_val (elit) >= 0)
      FATAL ("external reason clause must only contain falsified literals");
  }
  if (prop_elit && !propagated_lit_found)
    FATAL ("external reason clause must contain the propagated literal.");

  // copy the state from adding clauses to enable adding external clauses
  // everywhere.
  tmp_lrat_chain = std::move (lrat_chain);
  lrat_chain.clear ();
  tmp_clause = std::move (clause);
  clause.clear ();
  tmp_original = std::move (original);
  original.clear ();
  tmp_eclause = std::move (external->eclause);
  external->eclause.clear ();

  from_propagator = true;
  for (auto &tmp : tmp_elits)
    external->add (tmp);
  tmp_elits.clear ();
  from_propagator = false;

  // copy the old state back.
  assert (lrat_chain.empty ());
  assert (clause.empty ());
  assert (original.empty ());
  assert (external->eclause.empty ());
  lrat_chain = std::move (tmp_lrat_chain);
  clause = std::move (tmp_clause);
  original = std::move (tmp_original);
  external->eclause = std::move (tmp_eclause);
}

/*----------------------------------------------------------------------------*/
//
// Recursively calls 'learn_external_reason_clause' to explain every
// backward reachable externally propagated literal starting from 'ilit'.
//
void Internal::explain_reason (int ilit, Clause *reason, int &open) {
  if (!opts.exteagerreasons)
    return;
#ifndef NDEBUG
  LOG (reason, "explain_reason of %d (open: %d)", ilit, open);
#endif
  assert (reason);
  assert (reason != external_reason);
  for (const auto &other : *reason) {
    if (other == ilit)
      continue;
    Flags &f = flags (other);
    if (f.seen)
      continue;
    Var &v = var (other);
    if (!v.level)
      continue;
    assert (val (other) < 0);
    assert (v.level <= level);
    if (v.reason == external_reason) {
      v.reason = learn_external_reason_clause (-other);
    }
    if (v.level && v.reason) {
      f.seen = true;
      open++;
    }
  }
}

/*----------------------------------------------------------------------------*/
//
// In case external propagation was used, the reason clauses of the
// relevant propagations must be learned lazily before/during conflict
// analysis. While conflict analysis needs to analyze only the current
// level, lazy clause learning must check every clause on every level that
// is backward reachable from the conflicting clause to guarantee that the
// assignment levels of the variables are accurate. So this explanation
// round is separated from the conflict analysis, thereby guranteeing that
// the flags and datastructures can be properly used later.
//
// This function must be called before the conflict analysis, in order to
// guarantee that every relevant reason clause is indeed learned already
// and to be sure that the levels of assignments are set correctly.
//
// Later TODO: experiment with bounded explanation (explain only those
// literals that are directly used during conflict analysis +
// minimizing/shrinking). The assignment levels are then only
// over-approximated.
//
void Internal::explain_external_propagations () {
  assert (conflict);
  assert (clause.empty ());

  Clause *reason = conflict;
  std::vector<int> seen_lits;
  int open = 0; // Seen but not explained literal

  explain_reason (0, reason, open); // marks conflict clause lits as seen
  int i = trail.size ();            // Start at end-of-trail
  while (i > 0) {
    const int lit = trail[--i];
    if (!flags (lit).seen)
      continue;
    seen_lits.push_back (lit);
    Var &v = var (lit);
    if (!v.level)
      continue;
    if (v.reason) {
      open--;
      explain_reason (lit, v.reason, open);
    }
    if (!open)
      break;
  }
  assert (!open);

  if (!opts.exteagerrecalc) {
    for (auto lit : seen_lits) {
      Flags &f = flags (lit);
      f.seen = false;
    }
    seen_lits.clear ();
#ifndef NDEBUG
    for (auto idx : vars) {
      assert (!flags (idx).seen);
    }
#endif
  } else {
    assert (external_prop && !external_prop_is_lazy &&
            opts.exteagerreasons && opts.exteagerrecalc);
    // Traverse now in the opposite direction (from lower to higher
    // levels) and calculate the actual assignment level for the seen
    // assignments.
    for (auto it = seen_lits.rbegin (); it != seen_lits.rend (); ++it) {
      const int lit = *it;
      Flags &f = flags (lit);
      Var &v = var (lit);
      if (v.reason) {
        int real_level = 0;
        for (const auto &other : *v.reason) {
          if (other == lit)
            continue;
          int tmp = var (other).level;
          if (tmp > real_level)
            real_level = tmp;
        }
        if (v.level && !real_level) {
          build_chain_for_units (lit, v.reason, 1);
          learn_unit_clause (lit);
          lrat_chain.clear ();
          v.reason = 0;
        }
        assert (v.level >= real_level);
        if (v.level > real_level) {
          v.level = real_level;
        }
      }
      f.seen = false;
    }
  }

#if 0 // has been fuzzed extensively
  for (auto idx : vars) {
    assert (!flags (idx).seen);
  }
#endif
}

/*----------------------------------------------------------------------------*/
//
// Learns the reason clause of the propagation of ilit from the
// external propagator via 'add_external_clause'.
// In case of falsified propagation steps, if the propagated literal is
// already fixed to the opposite value, externalize will not necessarily
// give back the original elit (but an equivalent one). To avoid that, in
// falsified propagation cases the propagated elit is added as a second
// argument.
//
Clause *Internal::learn_external_reason_clause (int ilit,
                                                int falsified_elit) {
  assert (external->propagator); // REQ is defined by not allowing
                                 // unobserving during conflict

  stats.up_cb_prop_explain++;

  int elit = 0;
  if (!falsified_elit) {
    assert (!fixed (ilit));
    elit = externalize (ilit);
  } else
    elit = falsified_elit;

  // Propagation reason clauses are by default assumed to be forgettable
  // irredundant. In case they would be unforgettably important, the
  // propagator can add them as an explicit unforgettable external
  // clause or set 'are_reasons_forgettable' to false.
  ext_clause_forgettable = external->propagator->are_reasons_forgettable;
  LOG ("ilit: %d, elit: %d", ilit, elit);
  // we allow backtracking for conflicts
  if (!falsified_elit)
    force_no_backtrack = true;
  add_external_clause (elit);
  force_no_backtrack = false;

#ifndef NDEBUG
  if (!falsified_elit && newest_clause) {
    // Check if external propagation is correct wrt to the topological
    // order defined by the trail. In case it is a falsified external
    // propagation step, the order does not matter, the reason simply
    // supposed to be a falsified clause.
    const int propagated_ilit = ilit;
    for (auto const reason_ilit : *newest_clause) {
      assert (var (reason_ilit).trail <= var (propagated_ilit).trail);
    }
  }
#endif

  return newest_clause;
}

/*----------------------------------------------------------------------------*/
//
// Asks the external propagator if the current solution is OK
// by calling 'cb_check_found_model (model)'.
//
// If the external propagator approves the model, the function
// returns false.
//
// If the propagator does not approve the model, the solver asks
// the propagator to add external clauses.
//
// If the user does not add clauses or force a backtrack then
// the search will terminate with the found model, even if
// the user was initially unhappy.
bool Internal::external_check_solution () {
  if (!external_prop)
    return false;

  assert (notified_level == level);
  assert (notified_trail == trail.size ());

  // no need to extend because it cannot flip non-witness literals.
  // external->reset_extended ();
  // external->extend ();

  assert (notify_model_trail.empty ());

  for (int idx = 1; idx <= external->max_var; idx++) {
    if ((size_t) idx >= external->is_observed.size ())
      break;
    if (!external->is_observed[idx])
      continue;
    assert (!external->marked (external->witness, idx));
    const signed char tmp = external->current_val (idx);
    assert (tmp);
    const int lit = idx * tmp;
    notify_model_trail.push_back (lit);
  }

  LOG ("Final check by external propagator is invoked.");
  stats.up_cb++;
  stats.up_cb_check_model++;
  LOG_INTERACTION_START (cb_check_found_model);
  bool is_consistent =
      external->propagator->cb_check_found_model (notify_model_trail);
  LOG_INTERACTION_RETURN (cb_check_found_model, is_consistent);
  notify_model_trail.clear ();

  if (level < notified_level || notified_trail < trail.size ()) {
    stats.up_cb_forced++;
    return true;
  }
  if (is_consistent) {
    LOG ("Found solution is approved by external propagator.");
    return false;
  }

  // we still have a complete model but the user is unhappy
  // so they can add clauses.
  // cvc5 expects to continue so we can't do this:
  // return external_adding_clauses ();
  external_adding_clauses ();
  return true;
}

// Notify the external propagator that an observed variable got assigned.
// Returns false if the solver level stays, otherwise true.
//
// Fixed variables might get mapped (during compact) to another
// non-observed but fixed variable.
// This happens on root level, so notification about their assignment
// is already done.
bool Internal::notifying_assignments () {
  if (!external_prop || external_prop_is_lazy)
    return false;
  const size_t end_of_trail = trail.size ();

  assert (notified_trail <= end_of_trail);
  assert (level == notified_level);
  if (!level)
    notified_trail = 0;

  if (notified_trail == end_of_trail) {
    assert (delay_notify_units.empty ());
    LOG ("no new assignments to notify");
    return false;
  }

  LOG ("notify external propagator about new assignments");
  assert (notification_trail.empty ());

  for (auto &elit : delay_notify_units) {
    assert (!level);
    // already external.
    if (!external->observed (elit))
      continue;
    if (external->marked (external->notified, elit))
      continue;
    LOG ("marking fixed %d as notified", elit);
    external->mark (external->notified, elit);
    notification_trail.push_back (elit);
    if (opts.extnassign) {
      LOG_INTERACTION_FOR (notify_assignment, notification_trail[0]);
      external->propagator->notify_assignment (notification_trail);
      LOG_INTERACTION_END_FOR (notify_assignment, notification_trail[0]);
      notification_trail.clear ();
    }
  }
  assert (level == notified_level);
  delay_notify_units.clear ();
  while (notified_trail < end_of_trail) {
    const int ilit = trail[notified_trail++];
    if (!observed (ilit))
      continue;

    // TODO: double-check side-effects of externalize, e.g. tainting
    const int elit = externalize (ilit);
    assert (elit);

    assert (!external->ervars[abs (elit)]);

    assert (external->observed (elit) || fixed (ilit));
    if (!external->observed (elit))
      continue;
    // Make sure to only notify units once.
    if (external->marked (external->notified, elit)) {
      assert (!level);
      continue;
    }
    if (!level) {
      external->mark (external->notified, elit);
      LOG ("marking fixed %d as notified", elit);
    }
    notification_trail.push_back (elit);
    if (opts.extnassign) {
      LOG_INTERACTION_FOR (notify_assignment, notification_trail[0]);
      external->propagator->notify_assignment (notification_trail);
      LOG_INTERACTION_END_FOR (notify_assignment, notification_trail[0]);
      notification_trail.clear ();
      if (notified_level != level) {
        stats.up_notify_forced++;
        return true;
      }
    }
  }
  if (notification_trail.empty ())
    return false;
  stats.up_notify++;
  stats.up_notify_assignments++;
  LOG_INTERACTION_FOR (notify_assignment_batch,
                       (int) notification_trail.size ());
  external->propagator->notify_assignment (notification_trail);
  LOG_INTERACTION_END_FOR (notify_assignment_batch,
                           (int) notification_trail.size ());
  notification_trail.clear ();
  if (notified_level == level && notified_trail == trail.size ())
    return false;
  // Only here we actually changed the level or observed an already
  // assigned variable.
  stats.up_notify_forced++;
  return true;
}

/*----------------------------------------------------------------------------*/

void Internal::connect_propagator () {
  if (level)
    backtrack_without_updating_phases ();
}

/*----------------------------------------------------------------------------*/
//
// Notify the external propagator that a new decision level is started.
//
bool Internal::notifying_decision () {
  if (!external_prop || external_prop_is_lazy)
    return false;
  assert (notified_level == level);
  assert (notified_trail == trail.size ());
  stats.up_notify++;
  stats.up_notify_decision++;
  notified_level++;
  const int new_level = level + 1;
  assert (new_level == notified_level);
  LOG_INTERACTION_FOR (notify_new_decision_level, new_level);
  external->propagator->notify_new_decision_level ();
  LOG_INTERACTION_END_FOR (notify_new_decision_level, new_level);
  if (level < new_level - 1 || notified_level < new_level ||
      notified_trail < trail.size ()) {
    notify_loop ();
    stats.up_notify_forced++;
    return true;
  }
  return false;
}

void Internal::notify_loop () {
  if (!external_prop || external_prop_is_lazy)
    return;
  while (notifying_backtrack ())
    continue;
  while (notifying_assignments ())
    while (notifying_backtrack ())
      continue;
}

bool Internal::notifying_backtrack () {
  if (!external_prop || external_prop_is_lazy)
    return false;
  assert (notified_level >= level);
  if (notified_level == level)
    return false;
  // this call can potentially trigger an additional backtrack.
  stats.up_notify++;
  stats.up_notify_backtrack++;
  // force_no_backtrack = true;
  const int level_now = level;
  if (!opts.extnbacktrack)
    notified_level = level_now + 1;
  while (notified_level > level_now) {
    notified_level--;
    LOG_INTERACTION_FOR (notify_backtrack, notified_level);
    external->propagator->notify_backtrack (notified_level);
    LOG_INTERACTION_END_FOR (notify_backtrack, notified_level);
  }
  assert (notified_level == level_now);
  // force_no_backtrack = false;
  assert (notified_level >= level);
  if (notified_level == level)
    return false;
  assert (false);
  stats.up_notify_forced++;
  return true;
}

/*----------------------------------------------------------------------------*/
//
// Ask the external propagator if there is a suggested literal as next
// decision.
//
bool Internal::ask_decision () {
  if (!external_prop || external_prop_is_lazy)
    return 0;

  assert (notified_level == level + 1);
  assert (!unsat);
  assert (!conflict);
  stats.up_cb++;
  stats.up_cb_decide++;

  LOG_INTERACTION_START (cb_decide);
  int elit = external->propagator->cb_decide ();
  LOG_INTERACTION_RETURN (cb_decide, elit);

  assert (!level || level + 1 <= notified_level);
  if (notified_level != level + 1)
    return true;
  if (notified_trail != trail.size ())
    return true;

  if (!elit)
    return false;

  stats.up_cb_decided++;
  LOG ("external propagator proposes decision: %d", elit);

  if (!external->observed (elit))
    FATAL ("external decisions are only allowed over observed variables.");
  if (external->current_val (elit))
    FATAL (
        "external decisions are only allowed over unassigned variables.");

  assert (external->is_observed[abs (elit)]);

  // TODO: double-check side-effects of internalize.
  int ilit = external->internalize (elit);

  assert (observed (ilit));

  LOG ("Asking external propagator for decision returned: %d (internal: "
       "%d, fixed: %d, val: %d)",
       elit, ilit, fixed (ilit), val (ilit));

  search_assume_decision (ilit);
  assert (level == notified_level);
  return true;
}

/*----------------------------------------------------------------------------*/
//
// Check if the clause is a forgettable clause coming from the external
// propagator.
//
bool Internal::is_external_forgettable (int64_t id) {
  assert (opts.check);
  return (external->forgettable_original.find (id) !=
          external->forgettable_original.end ());
}

/*----------------------------------------------------------------------------*/
//
// When an external forgettable clause is deleted, it is marked in the
// 'forgettable_original' hash, so that the internal model checking can
// ignore it.
//
void Internal::mark_garbage_external_forgettable (int64_t id) {
  assert (opts.check);
  assert (is_external_forgettable (id));

  LOG (external->forgettable_original[id],
       "forgettable external lemma is deleted:");
  // Mark as removed by flipping the first flag to false.
  external->forgettable_original[id][0] = 0;
}

/*----------------------------------------------------------------------------*/
//
// Check that the literals in the clause are properly ordered. Used only
// internally for debug purposes.
//
void Internal::check_watched_literal_invariants () {
#ifndef NDEBUG
  int v0 = 0;
  int v1 = 0;

  if (val (clause[0]) > 0)
    v0 = 1;
  else if (val (clause[0]) < 0)
    v0 = -1;

  if (val (clause[1]) > 0)
    v1 = 1;
  else if (val (clause[1]) < 0)
    v1 = -1;
  assert (v0 >= v1);
#endif
  if (val (clause[0]) > 0) {
    if (val (clause[1]) > 0) { // Case 1: Both literals are satisfied
      // They are ordered by lower to higher decision level
      assert (var (clause[0]).level <= var (clause[1]).level);

      // Every other literal of the clause is either
      //    - satisfied at higher level
      //    - unassigned
      //    - falsified
      for (size_t i = 2; i < clause.size (); i++)
        assert (val (clause[i]) <= 0 ||
                (var (clause[1]).level <= var (clause[i]).level));

    } else if (val (clause[1]) ==
               0) { // Case 2: First satisfied, next unassigned

      // Every other literal of the clause is either
      //    - unassigned
      //    - falsified
      for (size_t i = 2; i < clause.size (); i++)
        assert (val (clause[i]) <= 0);

    } else { // Case 3: First satisfied, next falsified -> could have been
             // a reason of a previous propagation
      // Every other literal of the clause is falsified but at a lower
      // decision level
      for (size_t i = 2; i < clause.size (); i++)
        assert (val (clause[i]) < 0 &&
                (var (clause[1]).level >= var (clause[i]).level));
    }
  } else if (val (clause[0]) == 0) {
    if (val (clause[1]) == 0) { // Case 4: Both literals are unassigned

      // Every other literal of the clause is either
      //    - unassigned
      //    - falsified
      for (size_t i = 2; i < clause.size (); i++)
        assert (val (clause[i]) <= 0);

    } else { // Case 5: First unassigned, next falsified -> PROPAGATE
      // Every other literal of the clause is falsified but at a lower
      // decision level
      for (size_t i = 2; i < clause.size (); i++)
        assert (val (clause[i]) < 0 &&
                (var (clause[1]).level >= var (clause[i]).level));
    }
  } else {
    assert (val (clause[0]) < 0 &&
            val (clause[1]) < 0); // Case 6: Both literals are falsified

    // They are ordered by higher to lower decision level
    assert (var (clause[0]).level >= var (clause[1]).level);

    // Every other literal of the clause is falsified, but at a lower
    // level
    for (size_t i = 2; i < clause.size (); i++)
      assert (val (clause[i]) < 0 &&
              (var (clause[1]).level >= var (clause[i]).level));
  }
}

#ifndef NDEBUG

/*----------------------------------------------------------------------------*/
//
// An expensive function that can be used for deep-debug trail-related
// issues in mobical. Do not use it unless it is really unavoidable.
//
// eq_class contains all the merged external literals that are currently
// compacted to the internal literal of trail[0] and return true.
//
// In case trail[0] does not exists or is not on the root level, the
// function returns false (indicating that there was no merger literal
// found).
//
bool Internal::get_merged_literals (std::vector<int> &eq_class) {
  eq_class.clear ();

  if (!trail.size ())
    return false;

  int ilit = trail[0];
  size_t lit_level = var (ilit).level;

  if (!lit_level) {
    // Collect all the variables that are merged and mapped to that ilit
    int ivar = abs (ilit);
    for (auto id : external->e2i) {
      int o_elit = id.second;
      int o_ilit = id.first;
      int other = abs (o_elit);
      if (other == ivar) {
        if (o_elit == ilit)
          eq_class.push_back (o_ilit);
        else
          eq_class.push_back (-o_ilit);
      }
    }

    return true;
  }

  return false;
}

/*----------------------------------------------------------------------------*/
//
// Collect all external variables that are FIXED internally. Again an
// expensive function that should be called only for debugging in mobical.
//
// Do not use it unless it is really unavoidable.
//
void Internal::get_all_fixed_literals (std::vector<int> &fixed_lits) {
  fixed_lits.clear ();
  if (!trail.size ())
    return;

  for (auto id : external->e2i) {
    int ilit = id.second;
    int eidx = id.first;
    if (ilit && !external->ervars[eidx]) {
      Flags &f = flags (ilit);
      if (f.status == Flags::FIXED) {
        fixed_lits.push_back (vals[abs (ilit)] * eidx);
      }
    }
  }
}
#endif

} // namespace CaDiCaL
