#include "internal.hpp"

#include <algorithm>

namespace CaDiCaL {

#ifndef NTRACING
#define LOG_INTERACTION_START(NAME) LOG (#NAME " on level %d START", level);
#define LOG_INTERACTION_FOR(NAME, VAL) \
  LOG (#NAME "(%d) on level %d START", VAL, level)

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

#define LOG_INTERACTION_RETURN_FOR(NAME, VAL, RET) \
  do { \
    LOG (#NAME "(%d) returns %d on level %d END", VAL, RET, level); \
    if (!opts.exttracecalls) \
      break; \
    if (!external->trace_api_file) \
      break; \
    trace_api_call (external->trace_api_file, this, #NAME, VAL, RET); \
  } while (0)
#define LOG_INTERACTION_RETURN_TWO(NAME, RET1, RET2) \
  do { \
    LOG (#NAME " returns %d (%d) on level %d END", RET1, RET2, level); \
    if (!opts.exttracecalls) \
      break; \
    if (!external->trace_api_file) \
      break; \
    trace_api_call (external->trace_api_file, this, #NAME, RET1, RET2); \
  } while (0)
#define LOG_INTERACTION_END_FOR(NAME, VAL) \
  do { \
    LOG (#NAME "(%d) on level %d END", VAL, level); \
    if (!opts.exttracecalls) \
      break; \
    if (!external->trace_api_file) \
      break; \
    trace_api_call (external->trace_api_file, this, #NAME, VAL); \
  } while (0)
#define LOG_INTERACTION_RETURN(NAME, VAL) \
  do { \
    LOG (#NAME " returns %d on level %d END", VAL, level); \
    if (!opts.exttracecalls) \
      break; \
    if (!external->trace_api_file) \
      break; \
    trace_api_call (external->trace_api_file, this, #NAME, VAL); \
  } while (0)
#else
#define LOG_INTERACTION_START(NAME) LOG (#NAME " on level %d START", level)
#define LOG_INTERACTION_FOR(NAME, VAL) \
  LOG (#NAME "(%d) on level %d START", VAL, level)

#define LOG_INTERACTION_RETURN(NAME, VAL) \
  LOG (#NAME " returns %d on level %d END", VAL, level)
#define LOG_INTERACTION_RETURN_TWO(NAME, RET1, RET2) \
  LOG (#NAME " returns %d (%d) on level %d END", RET1, RET2, level)
#define LOG_INTERACTION_END_FOR(NAME, VAL) \
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
  if (ref < UINT_MAX) {
    ref++;
    LOG ("variable %d is observed %u times", idx, ref);
  } else
    LOG ("variable %d remains observed forever", idx);
  // TODO: instead of actually backtracking, it would be enough to notify
  // backtrack and re-play again every levels' notification to the
  // propagator
  if (val (ilit) && level && !fixed (ilit)) {
    // The variable is already assigned, but we can not send a notification
    // about it because it happened on an earlier decision level.
    // To not break the stack-like view of the trail, we simply backtrack to
    // undo this unnotifiable assignment.
    REQUIRE (!conflict,
             "can not observe assigned variable during conflict analysis");
    const int assignment_level = var (ilit).level;
    backtrack (assignment_level - 1);
  } else if (level && fixed (ilit)) {
    REQUIRE (!conflict,
             "can not observe fixed variable during conflict analysis");
    backtrack (0);
  }
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
    REQUIRE (
        !conflict,
        "can not unobserve assigned variable during conflict analysis");
    const int assignment_level = var (ilit).level;
    backtrack (assignment_level - 1);
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
    if (!changed_val) {
      changed_val = idx;
      continue;
    }
    assert (val (changed_val));
    if (var (idx).level < var (changed_val).level) {
      changed_val = idx;
    }
  }
}

void Internal::renotify_trail_after_ilb () {
  assert (opts.ilb);
  if (!external_prop || external_prop_is_lazy || !trail.size () ||
      !opts.ilb) {
    return;
  }
  LOG ("notify external propagator about new assignments (after ilb)");
#ifndef NDEBUG
  LOG ("(decision level: %d, trail size: %zd, notified %zd)", level,
       trail.size (), notified);
#endif
  renotify_full_trail ();
}

void Internal::renotify_trail_after_local_search () {
  if (!external_prop || external_prop_is_lazy || !trail.size ()) {
    return;
  }
  LOG ("notify external propagator about new assignments (after local "
       "search)");
#ifndef NDEBUG
  LOG ("(decision level: %d, trail size: %zd, notified %zd)", level,
       trail.size (), notified);
#endif
  renotify_full_trail ();
}

void Internal::renotify_full_trail_between_trail_pos (
    int start_level, int end_level, int propagator_level,
    std::vector<int> &assigned, bool start_new_level) {
  assert (assigned.empty ());
  int j = start_level;
#ifdef LOGGING
  LOG ("starting notification of level %d from trail %d .. %d",
       propagator_level, start_level, end_level);
#else
  (void) propagator_level;
#endif
  if (start_new_level) {
    if (assigned.size ()) {
      LOG_INTERACTION_FOR (notify_assignment_batch, (int) assigned.size ());
      external->propagator->notify_assignment (assigned);
      LOG_INTERACTION_END_FOR (notify_assignment_batch,
                               (int) assigned.size ());
    }
    assigned.clear ();
    notified_level++;
    LOG_INTERACTION_FOR (notify_new_decision_level, notified_level);
    external->propagator->notify_new_decision_level ();
    LOG_INTERACTION_END_FOR (notify_new_decision_level, notified_level);
  }
  for (; j < end_level; ++j) {
    int ilit = trail[j];
    // In theory, 0 ilit can happen due to pseudo-decision levels
    if (!ilit)
      continue;

    if (!observed (ilit))
      continue;

    int elit = externalize (ilit); // TODO: double-check tainting

    LOG ("notifying elit %d @ %d aka %s", propagator_level, elit,
         LOGLIT (ilit));
    assert (elit);
    // Fixed variables might get mapped (during compact) to another
    // non-observed but fixed variable.
    // This happens on root level, so notification about their assignment
    // is already done.
    assert (external->observed (elit) || fixed (ilit));
    if (!external->ervars[abs (elit)])
      assigned.push_back (elit);
  }

  if (assigned.size ()) {
    LOG_INTERACTION_FOR (notify_assignment_batch, (int) assigned.size ());
    external->propagator->notify_assignment (assigned);
    LOG_INTERACTION_END_FOR (notify_assignment_batch,
                             (int) assigned.size ());
  }
  assigned.clear ();
}

// It repeats ALL assignments of the trail, so the already notified
// root-level assignments will be notified multiple times.
//
// As CaDiCaL is missing some '0' seperators, it is important to go
// over slices from the control stack instead of going over the trail
// directly.
void Internal::renotify_full_trail () {
  const size_t end_of_trail = trail.size ();
  if (level) {
    notified = 0; // TODO: save the last notified root-level position
                  // somewhere and use it here
    if (notified_level)
      notify_backtrack (0);
  }
  std::vector<int> assigned;

  int propagator_level = 0;

  const int c_size = control.size ();
  { // first all root-level literals
    const int start_level = 0;
    const int end_level =
        (control.size () > 1 ? control[1].trail : end_of_trail);
    renotify_full_trail_between_trail_pos (
        start_level, end_level, propagator_level, assigned, false);
  }

  // notify all intermediate levels
  for (int i = 2; i < c_size; ++i) {
    const int start_level = control[i - 1].trail;
    const int end_level = control[i].trail;
    propagator_level++;
    LOG ("notification of %d", propagator_level);

    renotify_full_trail_between_trail_pos (
        start_level, end_level, propagator_level, assigned, true);
  }

  // and the current level if there is non-root level one
  if (level) {
    const int start_level = control.back ().trail;
    propagator_level++;
    renotify_full_trail_between_trail_pos (
        start_level, end_of_trail, propagator_level, assigned, true);
  }
  assert (propagator_level == level);
  notified = trail.size ();

  return;
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
  REQUIRE (forced_backt_allowed,
           "not allowed to force backtrack in that state of the solver.");
  REQUIRE (new_level >= 0,
           "the target level of a forced backtrack must be non-negative.");
  REQUIRE (level > 0 && new_level < level,
           "the target level of a forced backtrack must be smaller than "
           "the current decision level.");

#ifndef NDEBUG
  LOG ("external propagator forces backtrack to decision level"
       "%d (from level %d)",
       new_level, level);
#endif
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
  if (level)
    require_mode (SEARCH);
  assert (!unsat);

  size_t before = num_assigned;
  bool cb_repropagate_needed = true;
  while (cb_repropagate_needed && !conflict && external_prop &&
         !external_prop_is_lazy && !private_steps) {
#ifndef NDEBUG
    LOG ("external propagation starts (decision level: %d, trail size: "
         "%zd, notified %zd)",
         level, trail.size (), notified);
#endif
    cb_repropagate_needed = false;
    // external->reset_extended (); //TODO for inprocessing

    notify_assignments ();

    LOG_INTERACTION_START (cb_propagate);
    int elit = external->propagator->cb_propagate ();
    LOG_INTERACTION_RETURN (cb_propagate, elit);

    CB_REQUIRE (
        !elit || ((size_t) abs (elit) < external->is_observed.size () &&
                  external->is_observed[abs (elit)]),
        "cb_propagate", elit,
        "external propagations are only allowed over observed variables.");

    stats.ext_prop.ext_cb++;
    stats.ext_prop.eprop_call++;
    while (elit) {
      assert (external->is_observed[abs (elit)]);
      int ilit = external->e2i[abs (elit)];
      if (elit < 0)
        ilit = -ilit;
      int tmp = val (ilit);
#ifndef NDEBUG
      assert (fixed (ilit) || observed (ilit));
      LOG ("External propagation of e%d (i%d val: %d)", elit, ilit, tmp);
#endif
      if (!tmp) {
        // variable is not assigned, it can be propagated
        if (!level) {
          Clause *res = learn_external_reason_clause (ilit, elit);
#ifndef LOGGING
          LOG (res, "reason clause of external propagation of %d:", elit);
#endif
          (void) res;
        } else
          search_assign_external (ilit);
        stats.ext_prop.eprop_prop++;

        if (unsat || conflict)
          break;
        propagate ();
        if (unsat || conflict)
          break;
        notify_assignments ();
      } else if (tmp < 0) {
        LOG ("External propgation of %d is falsified under current trail",
             ilit);
        stats.ext_prop.eprop_conf++;
        int level_before = level;
        size_t assigned = num_assigned;
        Clause *res = learn_external_reason_clause (ilit, elit);
#ifndef LOGGING
        LOG (res, "reason clause of external propagation of %d:", elit);
#endif
        (void) res;
        bool trail_changed =
            (num_assigned != assigned || level != level_before ||
             propagated < trail.size ());

        if (unsat || conflict)
          break;

        if (trail_changed) {
          propagate ();
          if (unsat || conflict)
            break;
          notify_assignments ();
        }
      } // else (tmp > 0) -> the case of a satisfied literal is ignored
      LOG_INTERACTION_START (cb_propagate);
      elit = external->propagator->cb_propagate ();
      LOG_INTERACTION_RETURN (cb_propagate, elit);
      stats.ext_prop.ext_cb++;
      stats.ext_prop.eprop_call++;
    }

#ifndef NDEBUG
    LOG ("External propagation ends (decision level: %d, trail size: %zd, "
         "notified %zd)",
         level, trail.size (), notified);
#endif
    if (!unsat && !conflict) {
      int level_before = level;
      size_t assigned = num_assigned;
      bool has_external_clause = ask_external_clause ();
      // New observed variable might have triggered a backtrack during this
      // ask_external_clause call, so we need to propagate before continuing
      stats.ext_prop.ext_cb++;
      stats.ext_prop.elearn_call++;

      bool trail_changed =
          (num_assigned != assigned || level != level_before ||
           propagated < trail.size ());
      if (trail_changed) {
        propagate (); // unsat or conflict will be caught later
        if (!unsat || !conflict)
          notify_assignments ();
      }

#ifndef NDEBUG
      if (has_external_clause)
        LOG ("New external clauses are to be added.");
      else
        LOG ("No external clauses to be added.");
#endif

      while (has_external_clause) {
        level_before = level;
        assigned = num_assigned;

        add_external_clause (0);
        trail_changed =
            (num_assigned != assigned || level != level_before ||
             propagated < trail.size ());
        cb_repropagate_needed = true;

        if (unsat || conflict) {
          cb_repropagate_needed = false;
          break;
        }

        if (trail_changed) {
          propagate ();
          if (unsat || conflict) {
            cb_repropagate_needed = false;
            break;
          }

          notify_assignments ();
        }
        has_external_clause = ask_external_clause ();
        stats.ext_prop.ext_cb++;
        stats.ext_prop.elearn_call++;
      }
    }
#ifndef NDEBUG
    LOG ("External clause addition ends on decision level %d at trail "
         "size "
         "%zd (notified %zd)",
         level, trail.size (), notified);
#endif
  }
  if (before < num_assigned)
    did_external_prop = true;
  return !conflict;
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
  LOG_INTERACTION_RETURN_TWO (cb_has_external_clause, res,
                              ext_clause_forgettable);

  return res;
}
/*----------------------------------------------------------------------------*/
//
// Literals of the externally learned clause must be reordered based on the
// assignment levels of the literals.
// Returns the best clause idx (except ignore)
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
// clause literal by literal. In case propagated_elit is 0, it is about an
// external clause via 'cb_add_external_clause_lit'. Otherwise, it is about
// learning the reason of 'propagated_elit' via 'cb_add_reason_clause_lit'.
// The learned clause is simplified by the current root-level assignment
// (i.e. root-level falsified literals are removed, root satisfied clauses
// are skipped). Duplicate literals are removed, tauotologies are detected
// and skipped. It always adds the original (un-simplified) external clause
// to the proof as an input clause and
// the simplified version of it (except exceptions below) as a derived
// clause.
//
// In case the external clause, after simplifications, is satisfied, no
// clause is constructed, and the function returns 0. In case the external
// clause, after simplifications, is empty, no clause is constructed, unsat
// is set true and the function returns 0. In case the external clause,
// after simplifications, is unit, no clause is constructed,
// 'Internal::clause' has the unit literal (without 0) and the function
// returns 0.
//
// In every other cases a new clause is constructed and the pointer is in
// newest_clause
//
void Internal::add_external_clause (int propagated_elit,
                                    bool no_backtrack) {
  assert (original.empty ());
  int elit = 0;
  bool propagated_lit_found = false;

  if (propagated_elit) {
    // Propagation reason clauses are by default assumed to be forgettable
    // irredundant. In case they would be unforgettably important, the
    // propagator can add them as an explicit unforgettable external clause
    // or set 'are_reasons_forgettable' to false.
    ext_clause_forgettable = external->propagator->are_reasons_forgettable;
#ifndef NDEBUG
    LOG ("add external reason of propagated lit: %d", propagated_elit);
#endif
    LOG_INTERACTION_FOR (cb_add_reason_clause_lit, propagated_elit);
    elit = external->propagator->cb_add_reason_clause_lit (propagated_elit);
    LOG_INTERACTION_RETURN_FOR (cb_add_reason_clause_lit, propagated_elit,
                                elit);
    if (elit == propagated_elit)
      propagated_lit_found = true;

    CB_REQUIRE (!elit ||
                    ((size_t) abs (elit) < external->is_observed.size () &&
                     external->is_observed[abs (elit)]),
                "cb_add_reason_clause_lit", elit,
                "reason clause must contain only observed variables.");
  } else {
    LOG_INTERACTION_START (cb_add_external_clause_lit);
    elit = external->propagator->cb_add_external_clause_lit ();
    LOG_INTERACTION_RETURN (cb_add_external_clause_lit, elit);

    CB_REQUIRE (!elit ||
                    ((size_t) abs (elit) < external->is_observed.size () &&
                     external->is_observed[abs (elit)]),
                "cb_add_external_clause_lit", elit,
                "external clause must contain only observed variables.");
  }

  // we need to be build a new LRAT chain if we are already in the middle of
  // the analysis (like during failed assumptions)
  LOG (lrat_chain, "lrat chain before");
  std::vector<int64_t> lrat_chain_ext = std::move (lrat_chain);
  lrat_chain.clear ();
  clause.clear ();

  // Read out the external lemma into original and simplify it into clause
  assert (clause.empty ());
  assert (original.empty ());

  assert (!force_no_backtrack);
  assert (!from_propagator);
  force_no_backtrack = no_backtrack;
  from_propagator = true;
  while (elit) {
    external->add (elit);
    if (propagated_elit) {
      LOG_INTERACTION_FOR (cb_add_reason_clause_lit, propagated_elit);
      elit =
          external->propagator->cb_add_reason_clause_lit (propagated_elit);
      LOG_INTERACTION_RETURN_FOR (cb_add_reason_clause_lit, propagated_elit,
                                  elit);
      if (elit == propagated_elit)
        propagated_lit_found = true;
      CB_REQUIRE (
          !elit || ((size_t) abs (elit) < external->is_observed.size () &&
                    external->is_observed[abs (elit)]),
          "cb_add_reason_clause_lit", elit,
          "reason clause must contain only observed variables.");
    } else {
      LOG_INTERACTION_START (cb_add_external_clause_lit);
      elit = external->propagator->cb_add_external_clause_lit ();
      LOG_INTERACTION_RETURN (cb_add_external_clause_lit, elit);
      CB_REQUIRE (
          !elit || ((size_t) abs (elit) < external->is_observed.size () &&
                    external->is_observed[abs (elit)]),
          "cb_add_external_clause_lit", elit,
          "external clause must contain only observed variables.");
    }
  }
  external->add (elit);

  CB_REQUIRE (
      !propagated_elit || propagated_lit_found, "cb_add_reason_clause_lit",
      elit, "external reason clause must contain the propagated literal.");
#ifdef NCONTRACTS
  (void) propagated_lit_found;
#endif

  assert (original.empty ());
  assert (clause.empty ());
  force_no_backtrack = false;
  from_propagator = false;
  lrat_chain = std::move (lrat_chain_ext);
  LOG (lrat_chain, "lrat chain after");
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
      v.reason = learn_external_reason_clause (-other, 0, true);
    }
    if (v.level && v.reason) {
      f.seen = true;
      open++;
    }
  }
}

/*----------------------------------------------------------------------------*/
//
// In case external propagation was used, the reason clauses of the relevant
// propagations must be learned lazily before/during conflict analysis.
// While conflict analysis needs to analyze only the current level, lazy
// clause learning must check every clause on every level that is backward
// reachable from the conflicting clause to guarantee that the assignment
// levels of the variables are accurate. So this explanation round is
// separated from the conflict analysis, thereby guranteeing that the flags
// and datastructures can be properly used later.
//
// This function must be called before the conflict analysis, in order to
// guarantee that every relevant reason clause is indeed learned already and
// to be sure that the levels of assignments are set correctly.
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
    // Traverse now in the opposite direction (from lower to higher levels)
    // and calculate the actual assignment level for the seen assignments.
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
                                                int falsified_elit,
                                                bool no_backtrack) {
  assert (external->propagator); // REQ is defined by not allowing
                                 // unobserving during conflict
  // we cannot modify clause during analysis
  auto clause_tmp = std::move (clause);

  assert (clause.empty ());
  assert (original.empty ());

  stats.ext_prop.eprop_expl++;

  int elit = 0;
  if (!falsified_elit) {
    assert (!fixed (ilit));
    elit = externalize (ilit);
  } else
    elit = falsified_elit;

  LOG ("ilit: %d, elit: %d", ilit, elit);
  add_external_clause (elit, no_backtrack);

#ifndef NDEBUG
  if (!falsified_elit && newest_clause) {
    // Check if external propagation is correct wrt to the topological order
    // defined by the trail. In case it is a falsified external propagation
    // step, the order does not matter, the reason simply supposed to be a
    // falsified clause.
    const int propagated_ilit = ilit;
    for (auto const reason_ilit : *newest_clause) {
      assert (var (reason_ilit).trail <= var (propagated_ilit).trail);
    }
  }
#endif

  clause = std::move (clause_tmp);
  return newest_clause;
}

/*----------------------------------------------------------------------------*/
//
// Helper function to be able to call learn_external_reason_clause when the
// internal clause is already used in the caller side (for example during
// proof checking). These calls are assumed to be without a falsified elit.
// Dont use it in general instead of learn_external_reason_clause because it
// does not support the corner cases where a literal remains in clause.
//
Clause *Internal::wrapped_learn_external_reason_clause (int ilit) {
  Clause *res;
  std::vector<int64_t> chain_tmp{std::move (lrat_chain)};
  lrat_chain.clear ();
  if (clause.empty ()) {
    res = learn_external_reason_clause (ilit, 0, true);
  } else {
    std::vector<int> clause_tmp{std::move (clause)};
    clause.clear ();
    res = learn_external_reason_clause (ilit, 0, true);
    // The learn_external_reason clause can leave a literal in clause when
    // there is a falsified elit arg. Here it is not allowed to
    // happen.
    assert (clause.empty ());

    clause = std::move (clause_tmp);
    clause_tmp.clear ();
  }
  assert (lrat_chain.empty ());
  lrat_chain = std::move (chain_tmp);
  chain_tmp.clear ();
  return res;
}

/*----------------------------------------------------------------------------*/
//
// Checks if the new clause forces backtracking, new assignments or conflict
// analysis
//
void Internal::handle_external_clause (Clause *res, int64_t new_id) {
  if (from_propagator)
    stats.ext_prop.elearned++;
  if (from_propagator && !res)
    stats.ext_prop.elearn_unit++;
  // new unit clause. For now just backtrack.
  if (!res && (force_no_backtrack ||
               (val (clause[0]) > 0 && opts.elevate > 0 &&
                (opts.elevate > 1 || var (clause[0]).reason)))) {
    if (force_no_backtrack)
      did_external_prop = true;
    assert (level);
    assert (new_id);
    const int idx = vidx (clause[0]);
    assert (val (clause[0]) >= 0);
    assert (!flags (idx).eliminated ());
    Var &v = var (idx);
    assert (val (clause[0]));
    v.level = 0;
    v.reason = 0;
    LOG ("elevate %s to level 0", LOGLIT (idx));
    const unsigned uidx = vlit (clause[0]);
    if (lrat || frat)
      unit_clauses (uidx) = new_id;
    mark_fixed (clause[0]);
    return;
  }

  if (!res) {
    if (from_propagator)
      stats.ext_prop.elearn_prop++;
    const int lit = clause[0];
    assert (!val (lit) || var (lit).level);
    if (val (lit))
      backtrack_without_updating_phases (var (lit).level - 1);
    if (opts.elevate == -1 && val (lit))
      backtrack_without_updating_phases ();
    assert (!val (lit));
    assign_original_unit (new_id, lit);
    return;
  }

  // at level 0 we have to do nothing...
  if (!level)
    return;

  assert (res);
  assert (res->size >= 2);
  const int pos0 = res->literals[0];
  const int pos1 = res->literals[1];
  const int l1 = var (pos1).level;
  const int l0 = var (pos0).level;
  if (force_no_backtrack) {
    assert (from_propagator);
    assert (val (pos1) < 0);
    assert (val (pos0) >= 0);

    Var &v = var (pos0);
    if (v.level != l1) {
      stats.ext_prop.elearn_elevate++;
      LOG (res,
           "elevate assignment of %s from level %d to level %d with lazy "
           "reason clause",
           LOGLIT (pos0), l0, l1);
      LOG ("elevate %s to level %d", LOGLIT (pos0), l1);
    } else
      LOG (res, "add assignment %s lazy reason clause", LOGLIT (pos0));
    v.level = l1;
    return;
  }
  assert (!force_no_backtrack);

  if (val (pos1) >= 0) // do nothing
    return;

  if (val (pos0) < 0) { // conflicting
    assert (val (pos1) < 0);
    assert (0 < l1 && l1 <= var (pos0).level);
    if (opts.elevate == -1)
      backtrack_without_updating_phases (l1);
    // its better to backtrack instead of analyze without propagator
    // but analyze with propagaor
    if (val (pos0) && !from_propagator)
      backtrack_without_updating_phases (l0 - 1);
    else if (val (pos0) && from_propagator) {
      conflict = res;
      stats.ext_prop.elearn_conf++;
    }
    if (val (pos1) < 0 && !val (pos0))
      search_assign_driving (pos0, res);
    return;
  }

  if (!val (pos0)) { // propagating
    assert (val (pos1) < 0);
    if (opts.elevate == -1)
      backtrack_without_updating_phases (l1);
    if (val (pos1) < 0 && !val (pos0))
      search_assign_driving (pos0, res);
    return;
  }

  if (l0 <= l1) // no alternative reason
    return;

  assert (val (pos0) > 0); // elevating
  assert (val (pos1) < 0);

  // It would have propagated pos0 on an earlier level than it is
  // assigned

  // Find the highest literal based on trail-position of the clause

  size_t highest_idx = best_literal_to_watch (pos0, true);
  assert (highest_idx != 0);
  const int highest_literal = clause[highest_idx];

  // highest trail level variable
  const Var &m = var (highest_literal);
  assert (l0 >= m.level);

  // best watch variable
  Var &v = var (pos0);

  // out-of-order if best watch smaller highest.
  if (v.trail < m.trail && opts.elevate > 0) {
    assert (highest_idx);
    int *lits = res->literals;
    if (highest_idx != 1) {
      lits[1] = highest_literal;
      lits[highest_idx] = pos1;
    }
    if (from_propagator)
      stats.ext_prop.elearn_ooo++;
    LOG (res,
         "ignore out-of-order missed assignment of %s from level %d to "
         "level %d with new "
         "reason clause",
         LOGLIT (pos0), var (pos0).level, var (pos1).level);
    return;
  }

  // in order
  if (v.trail > m.trail && opts.elevate > 0 &&
      (opts.elevate > 1 || v.reason)) {
    // If v.trail == m.trail, then the propagated literal is the
    // maximum as well, so no need to backtrack we simply reassign the
    // reason and level of the propagation
    LOG (res,
         "elevate assignment of %s from level %d to level %d with new "
         "reason clause",
         LOGLIT (pos0), var (pos0).level, var (pos1).level);

    assert (l1 < l0);
    assert (var (pos1).trail < var (pos0).trail);
    assert (var (highest_literal).trail < var (pos0).trail);

    v.level = l1;
    v.reason = res;
    LOG ("elevate %s to level %d", LOGLIT (pos0), l1);

    if (from_propagator)
      stats.ext_prop.elearn_elevate++;

    if (out_of_order_level == -1 || l1 < out_of_order_level)
      out_of_order_level = l1;
    if (v.trail > out_of_order_trail)
      out_of_order_trail = v.trail;
    return;
  }

  // backtrack instead
  LOG (res,
       "backtrack due to missed assignment of %d from level %d to "
       "level %d with new reason clause",
       pos0, l0, l1);
  assert (!force_no_backtrack);

  if (opts.elevate == -1)
    backtrack_without_updating_phases (l1);
  else
    backtrack_without_updating_phases (l0 - 1);

  assert (!val (pos0) && val (pos1) < 0);
  search_assign_driving (pos0, res);

  assert (v.trail >= m.trail);
  assert (v.level == l1);
  assert (val (pos0) > 0 && val (pos1) < 0);
}

/*----------------------------------------------------------------------------*/
//
// Asks the external propagator if the current solution is OK
// by calling 'cb_check_found_model (model)'.
//
// The checked model is built up after everything is restored
// from the reconstruction stack and every variable is reactivated
// and so it is not just simply the trail (i.e. it can be expensive).
//
// If the external propagator approves the model, the function
// returns true.
//
// If the propagator does not approve the model, the solver asks
// the propagator to add an external clause.
// This external clause, however, does NOT have to be falsified by
// the current model. The possible cases and reactions are described
// below in the function. The possible states after that function:
// - A solution was found and accepted by the external propagator
// - A conflicting clause was learned from the external propagator
// - The empty clause was learned due to something new learned from
// the external propagator.
//
// In case only new variables were introduced, but no new clauses were
// added, the function will return without a conflict to the outer CDCL
// loop, where the new (not yet satisfied) variables are recognized and
// the search continues.
bool Internal::external_check_solution () {
  if (!external_prop)
    return true;

  bool trail_changed = true;
  bool added_new_clauses = false;
  while (trail_changed || added_new_clauses) {
    notify_assignments ();
    if (!satisfied ())
      break;
    trail_changed = false; // to be on the safe side
    added_new_clauses = false;
    LOG ("Final check by external propagator is invoked.");
    stats.ext_prop.echeck_call++;
    external->reset_extended ();
    external->extend ();

    std::vector<int> etrail;

    // Here the variables must be filtered by external->is_observed,
    // because fixed variables are internally not necessarily observed
    // anymore.
    for (int idx = 1;
         idx <= std::min ((int) external->is_observed.size () - 1,
                          external->max_var);
         idx++) {
      if (!external->is_observed[idx])
        continue;
      const int lit = external->ival (idx);
      etrail.push_back (lit);
#ifndef NDEBUG
#ifdef LOGGING
      bool p = external->vals[idx];
      LOG ("evals[%d]: %d ival(%d): %d", idx, p, idx, lit);
#endif
#endif
    }

    forced_backt_allowed = true;
    size_t assigned = num_assigned;
    int level_before = level;
    LOG_INTERACTION_START (cb_check_found_model);
    bool is_consistent =
        external->propagator->cb_check_found_model (etrail);
    LOG_INTERACTION_RETURN (cb_check_found_model, is_consistent);
    stats.ext_prop.ext_cb++;
    forced_backt_allowed = false;

    if (num_assigned != assigned || level != level_before ||
        propagated < trail.size ()) {
      // In case an external forced backtracking was performed, the CDCL
      // loop needs to continue withouth further checks of the model.
      trail_changed = true;
      return !conflict;
    }

    if (is_consistent) {
      LOG ("Found solution is approved by external propagator.");
      return true;
    }

    bool has_external_clause = ask_external_clause ();

    stats.ext_prop.ext_cb++;
    stats.ext_prop.elearn_call++;

    if (has_external_clause)
      LOG (
          "Found solution triggered new clauses from external propagator.");

    while (has_external_clause) {
      level_before = level;
      assigned = num_assigned;
      add_external_clause (0);
      bool trail_changed =
          (num_assigned != assigned || level != level_before ||
           propagated < trail.size ());
      added_new_clauses = true;
      //
      // There are many possible scenarios here:
      // - Learned conflicting clause: return to CDCL loop (conflict true)
      // - Learned conflicting unit clause that after backtrack+BCP leads to
      //   a new complete solution: force the outer loop to check the new
      //   model (trail_changed is true, but (conflict & unsat) is false)
      // - Learned empty clause: return to CDCL loop (unsat true)
      // - Learned a non-conflicting unit clause:
      //   Though it does not invalidate the current solution, the solver
      //   will backtrack to the root level and will repropagate it. The
      //   search will start again (saved phases hopefully make it quick),
      //   but it is needed in order to guarantee that every fixed variable
      //   is properly handled+notified (important for incremental use
      //   cases).
      // - Otherwise: the solution is considered approved and the CDCL-loop
      //   can return with res = 10.
      //
      if (unsat || conflict || trail_changed)
        break;
      has_external_clause = ask_external_clause ();
      stats.ext_prop.ext_cb++;
      stats.ext_prop.elearn_call++;
    }
    LOG ("No more external clause to add.");
    if (unsat || conflict)
      break;
  }

  if (!unsat && conflict) {
    const int conflict_level = var (conflict->literals[0]).level;
    if (conflict_level != level) {
      backtrack (conflict_level);
    }
  }

  return !conflict;
}

/*----------------------------------------------------------------------------*/
//
// Notify the external propagator that an observed variable got assigned.
//
void Internal::notify_assignments () {
  if (!external_prop || external_prop_is_lazy || private_steps)
    return;

  const size_t end_of_trail = trail.size ();

  if (notified >= end_of_trail)
    return;

  LOG ("notify external propagator about new assignments");
  std::vector<int> assigned;

  while (notified < end_of_trail) {
    int ilit = trail[notified++];
    if (!observed (ilit))
      continue;

    int elit = externalize (ilit); // TODO: double-check tainting
    assert (elit);
    if (external->ervars[abs (elit)])
      continue;
    // Fixed variables might get mapped (during compact) to another
    // non-observed but fixed variable.
    // This happens on root level, so notification about their assignment is
    // already done.
    assert (external->observed (elit) ||
            (fixed (ilit) && !external->ervars[abs (elit)]));
    assigned.push_back (elit);
  }
  if (assigned.size ()) {
    LOG_INTERACTION_FOR (notify_assignment_batch, (int) assigned.size ());
    external->propagator->notify_assignment (assigned);
    LOG_INTERACTION_END_FOR (notify_assignment_batch,
                             (int) assigned.size ());
  }
  assigned.clear ();
  return;
}

/*----------------------------------------------------------------------------*/

void Internal::connect_propagator () {
  if (level)
    backtrack ();
}

/*----------------------------------------------------------------------------*/
//
// Notify the external propagator that a new decision level is started.
//
void Internal::notify_decision () {
  if (!external_prop || external_prop_is_lazy || private_steps)
    return;
  notify_assignments ();
  notified_level = level;
  LOG_INTERACTION_FOR (notify_new_decision_level, level);
  external->propagator->notify_new_decision_level ();
  LOG_INTERACTION_END_FOR (notify_new_decision_level, level);
}

/*----------------------------------------------------------------------------*/
//
// Notify the external propagator that backtrack to new_level.
//
void Internal::notify_backtrack (size_t new_level) {
  if (!external_prop || external_prop_is_lazy || private_steps)
    return;
  assert ((size_t) notified_level > new_level);
  LOG_INTERACTION_FOR (notify_backtrack, (int) new_level);
  external->propagator->notify_backtrack (new_level);
  LOG_INTERACTION_END_FOR (notify_backtrack, (int) new_level);
  notified_level = new_level;
}

/*----------------------------------------------------------------------------*/
//
// Ask the external propagator if there is a suggested literal as next
// decision.
//
int Internal::ask_decision () {
  if (!external_prop || external_prop_is_lazy || private_steps)
    return 0;

  assert (!unsat);
  assert (!conflict);
  notify_assignments ();
  int level_before = level;
  forced_backt_allowed = true;
  LOG_INTERACTION_START (cb_decide);
  int elit = external->propagator->cb_decide ();
  LOG_INTERACTION_RETURN (cb_decide, elit);
  forced_backt_allowed = false;
  stats.ext_prop.ext_cb++;

  if (level_before != level) {

    propagate ();
    assert (!unsat);
    assert (!conflict);
    notify_assignments ();

    // In case the external propagator forced to backtrack below the
    // pseduo decision levels, we must go back to the CDCL loop instead of
    // making a decision.
    if ((size_t) level < assumptions.size () ||
        ((size_t) level == assumptions.size () && constraint.size ())) {
      return 0;
    }
  }

  if (!elit)
    return 0;
  LOG ("external propagator proposes decision: %d", elit);

  CB_REQUIRE (
      (size_t) abs (elit) < external->is_observed.size () &&
          external->is_observed[abs (elit)],
      "cb_decide", elit,
      "external decisions are only allowed over observed variables.");

  assert (external->is_observed[abs (elit)]);

  int ilit = external->e2i[abs (elit)];
  if (elit < 0)
    ilit = -ilit;

  assert (fixed (ilit) || observed (ilit));

  LOG ("Asking external propagator for decision returned: %d (internal: "
       "%d, fixed: %d, val: %d)",
       elit, ilit, fixed (ilit), val (ilit));

  CB_REQUIRE (
      !fixed (ilit) && !val (ilit), "cb_decide", elit,
      "external decisions are only allowed over unassigned variables.");

  return ilit;
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

    } else { // Case 3: First satisfied, next falsified -> could have been a
             // reason of a previous propagation
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

    // Every other literal of the clause is falsified, but at a lower level
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
    size_t e2i_size = external->e2i.size ();
    int ivar = abs (ilit);
    for (size_t i = 0; i < e2i_size; i++) {
      int other = abs (external->e2i[i]);
      if (other == ivar) {
        if (external->e2i[i] == ilit)
          eq_class.push_back (i);
        else
          eq_class.push_back (-1 * i);
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

  int e2i_size = external->e2i.size ();
  int ilit;
  for (int eidx = 1; eidx < e2i_size; eidx++) {
    ilit = external->e2i[eidx];
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
