#include "internal.hpp"

namespace CaDiCaL {

// The idea of warmup is to reuse the strength of CDCL, namely
// propagating, before calling random walk that is not good at
// propagating long chains. Therefore, we propagate (ignoring all conflicts)
// discovered along the way.
// The asignmend is the same as the normal assignment however, it updates the target phases so that local search can pick them up later

// specific warmup version with saving of the target.
inline void Internal::warmup_assign (int lit, Clause *reason) {

  assert (level); // no need to learn unit clauses here
  require_mode (SEARCH);

  const int idx = vidx (lit);
  assert (reason != external_reason);
  assert (!vals[idx]);
  assert (!flags (idx).eliminated () || reason == decision_reason);
  assert (!searching_lucky_phases);
  assert (lrat_chain.empty());
  Var &v = var (idx);
  int lit_level;
  assert (!(reason == external_reason &&
	    ((size_t) level <= assumptions.size () + (!!constraint.size ()))));
  assert (reason);
  assert (level || reason == decision_reason);
  // we  purely assign in order here
  lit_level = level;

  v.level = lit_level;
  v.trail = trail.size();
  v.reason = reason;
  assert ((int) num_assigned < max_var);
  assert (num_assigned == trail.size ());
  num_assigned++;
  const signed char tmp = sign (lit);
  phases.saved[idx] = tmp;
  set_val (idx, tmp);
  assert (val (lit) > 0);
  assert (val (-lit) < 0);

  trail.push_back (lit);
#ifdef LOGGING
  if (!lit_level)
    LOG ("root-level unit assign %d @ 0", lit);
  else
    LOG (reason, "search assign %d @ %d", lit, lit_level);
#endif

  assert (watching ());
  const Watches &ws = watches (-lit);
  if (!ws.empty ()) {
    const Watch &w = ws[0];
    __builtin_prefetch (&w, 0, 1);
  }
}


void Internal::warmup_propagate_beyond_conflict () {

  assert (!unsat);

  START (propagate);
  assert (!ignore);

  int64_t before = propagated;

  while (propagated != trail.size ()) {

    const int lit = -trail[propagated++];
    LOG ("propagating %d", -lit);
    Watches &ws = watches (lit);

    const const_watch_iterator eow = ws.end ();
    watch_iterator j = ws.begin ();
    const_watch_iterator i = j;

    while (i != eow) {

      const Watch w = *j++ = *i++;
      const signed char b = val (w.blit);

      if (b > 0)
        continue; // blocking literal satisfied

      if (w.binary ()) {

        // In principle we can ignore garbage binary clauses too, but that
        // would require to dereference the clause pointer all the time with
        //
        // if (w.clause->garbage) { j--; continue; } // (*)
        //
        // This is too costly.  It is however necessary to produce correct
        // proof traces if binary clauses are traced to be deleted ('d ...'
        // line) immediately as soon they are marked as garbage.  Actually
        // finding instances where this happens is pretty difficult (six
        // parallel fuzzing jobs in parallel took an hour), but it does
        // occur.  Our strategy to avoid generating incorrect proofs now is
        // to delay tracing the deletion of binary clauses marked as garbage
        // until they are really deleted from memory.  For large clauses
        // this is not necessary since we have to access the clause anyhow.
        //
        // Thanks go to Mathias Fleury, who wanted me to explain why the
        // line '(*)' above was in the code. Removing it actually really
        // improved running times and thus I tried to find concrete
        // instances where this happens (which I found), and then
        // implemented the described fix.

        // Binary clauses are treated separately since they do not require
        // to access the clause at all (only during conflict analysis, and
        // there also only to simplify the code).

        if (b < 0)
          ;// conflict = w.clause; // ignoring conflict
        else {
          warmup_assign (w.blit, w.clause);
        }

      } else {
        assert (w.clause->size > 2);

        // The cache line with the clause data is forced to be loaded here
        // and thus this first memory access below is the real hot-spot of
        // the solver.  Note, that this check is positive very rarely and
        // thus branch prediction should be almost perfect here.

        if (w.clause->garbage) {
          j--;
          continue;
        }
        literal_iterator lits = w.clause->begin ();
        const int other = lits[0] ^ lits[1] ^ lit;
        const signed char u = val (other);
        if (u > 0)
          j[-1].blit = other;
        else {
          const int size = w.clause->size;
          const const_literal_iterator end = lits + size;
          const literal_iterator middle = lits + w.clause->pos;
          literal_iterator k = middle;
          signed char v = -1;
          int r = 0;
          while (k != end && (v = val (r = *k)) < 0)
            k++;
          if (v < 0) {
            k = lits + 2;
            assert (w.clause->pos <= size);
            while (k != middle && (v = val (r = *k)) < 0)
              k++;
          }

          w.clause->pos = k - lits; // always save position

          assert (lits + 2 <= k), assert (k <= w.clause->end ());

          if (v > 0) {

            // Replacement satisfied, so just replace 'blit'.

            j[-1].blit = r;

          } else if (!v) {

            // Found new unassigned replacement literal to be watched.

            LOG (w.clause, "unwatch %d in", lit);

            lits[0] = other;
            lits[1] = r;
            *k = lit;

            watch_literal (r, lit, w.clause);

            j--; // Drop this watch from the watch list of 'lit'.

          } else if (!u) {

            assert (v < 0);

            // The other watch is unassigned ('!u') and all other literals
            // assigned to false (still 'v < 0'), thus we found a unit.
            //
            build_chain_for_units (other, w.clause, 0);
            warmup_assign (other, w.clause);

            // Similar code is in the implementation of the SAT'18 paper on
            // chronological backtracking but in our experience, this code
            // first does not really seem to be necessary for correctness,
            // and further does not improve running time either.
            //
            if (opts.chrono > 1) {

              const int other_level = var (other).level;

              if (other_level > var (lit).level) {

                // The assignment level of the new unit 'other' is larger
                // than the assignment level of 'lit'.  Thus we should find
                // another literal in the clause at that higher assignment
                // level and watch that instead of 'lit'.

                assert (size > 2);

                int pos, s = 0;

                for (pos = 2; pos < size; pos++)
                  if (var (s = lits[pos]).level == other_level)
                    break;

                assert (s);
                assert (pos < size);

                LOG (w.clause, "unwatch %d in", lit);
                lits[pos] = lit;
                lits[0] = other;
                lits[1] = s;
                watch_literal (s, other, w.clause);

                j--; // Drop this watch from the watch list of 'lit'.
              }
            }
          } else {

            assert (u < 0);
            assert (v < 0);

	    // ignoring conflict
          }
        }
      }
    }
  }

  assert (propagated == trail.size ());

  stats.warmup.propagated += (trail.size() - before);
  STOP (propagate);
}


int Internal::warmup_decide () {
  assert (!satisfied ());
  START (decide);
  int res = 0;
  if ((size_t) level < assumptions.size ()) {
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
      new_trail_level (lit);
      search_assume_decision (lit);
    }
  } else if ((size_t) level == assumptions.size () && constraint.size ()) {

    int satisfied_lit = 0;  // The literal satisfying the constrain.
    int unassigned_lit = 0; // Highest score unassigned literal.
    int previous_lit = 0;   // Move satisfied literals to the front.

    const size_t size_constraint = constraint.size ();

#ifndef NDEBUG
    unsigned sum = 0;
    for (auto lit : constraint)
      sum += lit;
#endif
    for (size_t i = 0; i != size_constraint; i++) {

      // Get literal and move 'constraint[i] = constraint[i-1]'.

      int lit = constraint[i];
      constraint[i] = previous_lit;
      previous_lit = lit;

      const signed char tmp = val (lit);
      if (tmp < 0) {
        LOG ("constraint literal %d falsified", lit);
        continue;
      }

      if (tmp > 0) {
        LOG ("constraint literal %d satisfied", lit);
        satisfied_lit = lit;
        break;
      }

      assert (!tmp);
      LOG ("constraint literal %d unassigned", lit);

      if (!unassigned_lit || better_decision (lit, unassigned_lit))
        unassigned_lit = lit;
    }

    if (satisfied_lit) {

      constraint[0] = satisfied_lit; // Move satisfied to the front.

      LOG ("literal %d satisfies constraint and "
           "is implied by assumptions",
           satisfied_lit);

      new_trail_level (0);
      LOG ("added pseudo decision level for constraint");
      notify_decision ();

    } else {

      // Just move all the literals back.  If we found an unsatisfied
      // literal then it will be satisfied (most likely) at the next
      // decision and moved then to the first position.

      if (size_constraint) {

        for (size_t i = 0; i + 1 != size_constraint; i++)
          constraint[i] = constraint[i + 1];

        constraint[size_constraint - 1] = previous_lit;
      }

      if (unassigned_lit) {

        LOG ("deciding %d to satisfy constraint", unassigned_lit);
        search_assume_decision (unassigned_lit);

      } else {

        LOG ("failing constraint");
        unsat_constraint = true;
        res = 20;
      }
    }

#ifndef NDEBUG
    for (auto lit : constraint)
      sum -= lit;
    assert (!sum); // Checksum of literal should not change!
#endif

  } else {
    const bool target = (stable || opts.target == 2);
    stats.warmup.decision++;
    int idx = next_decision_variable ();
    if (flags (idx).eliminated ())
      ++stats.warmup.dummydecision;
    int decision = decide_phase (idx, target);
    new_trail_level (decision);
    warmup_assign (decision, decision_reason);
  }
  if (res)
    marked_failed = false;
  STOP (decide);
  return res;
}

int Internal::warmup () {
  assert (!unsat);
  assert (!level);
  if (!opts.warmup)
    return 0;
  require_mode(WALK);
  START (warmup);
  ++stats.warmup.count;
  assert (!private_steps);
  private_steps = true;
  int res = 0;

#ifndef QUIET
  const int64_t warmup_propagated = stats.warmup.propagated;
  const int64_t decision = stats.warmup.decision;
  const int64_t dummydecision = stats.warmup.dummydecision;
#endif
  assert (propagated == trail.size ());
  LOG ("propagating beyond conflicts to warm-up walk");
  while (!res && num_assigned < (size_t) max_var) {
    assert (propagated == trail.size ());
    res = warmup_decide ();
    warmup_propagate_beyond_conflict();
    LOG (lrat_chain, "during warmup with lrat chain:");
  }
  assert (res || num_assigned == (size_t) max_var);
#ifndef QUIET
  // constrains with empty levels break this
  // assert (res || stats.warmup.propagated - warmup_propagated == (int64_t)num_assigned);
  VERBOSE (3, "warming-up needed %" PRIu64 " propagations including %" PRIu64 " decisions (with %" PRIu64 " dummy ones)",
	   stats.warmup.propagated - warmup_propagated,
	   stats.warmup.decision - decision,
	   stats.warmup.dummydecision - dummydecision);
#endif

  if (!res)
    backtrack_without_updating_phases ();
  private_steps = false;
  STOP (warmup);
  require_mode(WALK);
  return res;
}

}
