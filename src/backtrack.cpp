#include "internal.hpp"
#include <vector>

namespace CaDiCaL {

// The global assignment stack can only be (partially) reset through
// 'backtrack' which is the only function using 'unassign' (inlined and thus
// local to this file).  It turns out that 'unassign' does not need a
// specialization for 'probe' nor 'vivify' and thus it is shared.

inline void Internal::unassign (int lit) {
  assert (val (lit) > 0);
  set_val (lit, 0);
  var (lit).missed_implication = nullptr;
  var (lit).missed_level = -1;
  var (lit).dirty = false;

  int idx = vidx (lit);
  LOG ("unassign %d @ %d", lit, var (idx).level);
  num_assigned--;

  // In the standard EVSIDS variable decision heuristic of MiniSAT, we need
  // to push variables which become unassigned back to the heap.
  //
  if (!scores.contains (idx))
    scores.push_back (idx);

  // For VMTF we need to update the 'queue.unassigned' pointer in case this
  // variable sits after the variable to which 'queue.unassigned' currently
  // points.  See our SAT'15 paper for more details on this aspect.
  //
  if (queue.bumped < btab[idx])
    update_queue_unassigned (idx);
}

/*------------------------------------------------------------------------*/

// Update the current target maximum assignment and also the very best
// assignment.  Whether a trail produces a conflict is determined during
// propagation.  Thus that all functions in the 'search' loop after
// propagation can assume that 'no_conflict_until' is valid.  If a conflict
// is found then the trail before the last decision is used (see the end of
// 'propagate').  During backtracking we can then save this largest
// propagation conflict free assignment.  It is saved as both 'target'
// assignment for picking decisions in 'stable' mode and if it is the
// largest ever such assignment also as 'best' assignment. This 'best'
// assignment can then be used in future stable decisions after the next
// 'rephase_best' overwrites saved phases with it.

void Internal::update_target_and_best () {

  bool reset = (rephased && stats.conflicts > last.rephase.conflicts);

  if (reset) {
    target_assigned = 0;
    if (rephased == 'B')
      best_assigned = 0; // update it again
  }

  if (no_conflict_until > target_assigned) {
    copy_phases (phases.target);
    target_assigned = no_conflict_until;
    LOG ("new target trail level %zu", target_assigned);
  }

  if (no_conflict_until > best_assigned) {
    copy_phases (phases.best);
    best_assigned = no_conflict_until;
    LOG ("new best trail level %zu", best_assigned);
  }

  if (reset) {
    report (rephased);
    rephased = 0;
  }
}

/*------------------------------------------------------------------------*/

void Internal::backtrack (int new_level) {

  assert (new_level >= 0);
  assert (new_level <= level);
  if (new_level == level)
    return;

  stats.backtracks++;
  update_target_and_best ();

  assert (num_assigned == trail.size ());

  const size_t assigned = control[new_level + 1].trail;

  LOG ("backtracking to decision level %d with decision %d and trail %zd",
       new_level, control[new_level].decision, assigned);

  const size_t end_of_trail = trail.size ();
  size_t i = assigned, j = i;

#ifdef LOGGING
  int unassigned = 0;
#endif
  int reassigned = 0;

  notify_backtrack (new_level);
  std::vector<int> missed_props;
  if (external_prop && !external_prop_is_lazy && notified > assigned) {
    LOG ("external propagator is notified about some unassignments (trail: "
         "%zd, notified: %zd).",
         trail.size (), notified);
    notified = assigned;
  }

  int earliest_dirty = trail.size();

  while (i < end_of_trail) {
    int lit = trail[i++];
    Var &v = var (lit);
    if (opts.chrono == 3 && v.missed_implication && v.level > new_level && v.missed_level <= new_level) {
      if (v.missed_implication)
        assert (v.missed_level <= level && opts.chrono == 3);
      assert (v.missed_level <= level && opts.chrono == 3);
      assert (opts.chrono == 3);
      LOG (v.missed_implication,
           "BT missed lower-level implication of %d at level %d (was %d)",
           lit, var (lit).missed_level, var (lit).level);
      LOG (v.reason, "other reason");
      assert (external_prop || var (lit).missed_level < var (lit).level);
      for (auto other : *v.missed_implication) {
        LOG ("lit %d at level %d", other, var (other).level);
        if (other != lit)
          assert (val (other) < 0);
      }
      missed_props.push_back (lit);
      LOG ("setting literal %d dirty", lit);
      v.dirty = true;
    }
    else if (v.level > new_level) {
      unassign (lit);
#ifdef LOGGING
      unassigned++;
#endif
    } else {
      // This is the essence of the SAT'18 paper on chronological
      // backtracking.  It is possible to just keep out-of-order assigned
      // literals on the trail without breaking the solver (after some
      // modifications to 'analyze' - see 'opts.chrono' guarded code there).
      assert (opts.chrono || external_prop || did_external_prop);
      if (v.missed_implication && v.missed_level > new_level) {
	//we are going further back that the missed suggests: deleting
        LOG (v.missed_implication,
             "BT resetting missed of lit %d @ %d is not reused (expected "
             "level "
             "%d), target level: %d",
             lit, v.level, v.missed_level, new_level);
        v.missed_implication = nullptr; // happens notably for units
      }
#ifdef LOGGING
      if (!v.level)
        LOG ("reassign %d @ 0 unit clause %d", lit, lit);
      else
        LOG (v.reason, "reassign %d @ %d", lit, v.level);
#endif
      trail[j] = lit;
      v.trail = j++;
      reassigned++;
      if (opts.chrono == 3 && v.dirty && j < earliest_dirty) {
        LOG ("found dirty literal %d at %d", lit, j - 1);
        earliest_dirty = j - 1;
      }
    }
  }
  trail.resize (j);
  LOG ("unassigned %d literals %.0f%%", unassigned,
       percent (unassigned, unassigned + reassigned));
  LOG ("reassigned %d literals %.0f%%", reassigned,
       percent (reassigned, unassigned + reassigned));

  if (propagated > assigned)
    propagated = assigned;
  if (propagated2 > assigned)
    propagated2 = assigned;
  if (no_conflict_until > assigned)
    no_conflict_until = assigned;

  propergated = 0; // Always go back to root-level.

  assert (notified <= assigned + reassigned);
  if (reassigned) {
    notify_assignments ();
  }

  control.resize (new_level + 1);
  level = new_level;
  if (tainted_literal) {
    assert (opts.ilb);
    if (!val (tainted_literal)) {
      tainted_literal = 0;
    }
  }

  if (opts.chrono == 3) {
#if 0
    std::sort (std::begin (missed_props), std::end (missed_props),
            [this] (int litA, int litB) {
              return var (litA).missed_level < var (litB).missed_level ||
		     (var (litA).missed_level == var (litB).missed_level &&
		      var (litA).trail < var (litB).trail);});
#endif
    for (int i = missed_props.size() - 1; i >= 0; --i) {
      const int lit = missed_props[i];
      Var &v = var (lit);
      assert (v.missed_implication);
      ++stats.missedprops;
      assert (val (lit) > 0);
      assert (val (-lit) < 0);
      if (!v.missed_level && !unsat) {
	std::vector<uint64_t> lrat_chain_tmp (std::move (lrat_chain)); lrat_chain.clear();
	build_chain_for_units (lit, v.missed_implication, true);
	learn_unit_clause (lit);
	lrat_chain = std::move (lrat_chain_tmp);
	// not marking the clause garbage, because it can be involved in the conflict analysis
	LOG (lrat_chain, "chain set back to: ");
      }
      v.reason = v.missed_level ? v.missed_implication : 0;
      assert (level >= v.missed_level);
      v.level = v.missed_level;
      assert (new_level >= v.missed_level);
      v.trail = trail.size();
      if (v.missed_level)
	LOG (v.reason,
             "setting missed propagation lit %d at level %d with reason", lit, v.level);
      else
	LOG ("setting missed propagation lit %d to root level", lit, v.level);
      if (v.dirty) {
	LOG ("lit %d is dirty", lit);
	earliest_dirty = std::min (earliest_dirty, (int)trail.size());
      }
      trail.push_back (lit);
      var (lit).missed_implication = nullptr;
    }
    if (!missed_props.empty ())
      notify_assignments ();
  }

  if (opts.chrono == 3) {
    LOG ("strong chrono: %ld repropagations",
         trail.size () - earliest_dirty);
    LOG ("setting propagated to %d", earliest_dirty);
    if (earliest_dirty > trail.size())
      earliest_dirty = num_assigned;
    LOG ("setting propagated to %d (first lit: %d)", earliest_dirty, earliest_dirty < trail.size() ? trail[earliest_dirty] : 0);
    propagated = earliest_dirty;
    propagated2 = earliest_dirty;
    no_conflict_until = earliest_dirty;
  }
  assert (num_assigned == trail.size ());
}

} // namespace CaDiCaL
