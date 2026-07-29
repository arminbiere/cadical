#include "internal.hpp"
#include "kitten.h"

namespace CaDiCaL {

void Internal::constrain (int lit) {
  if (unsat)
    return;
  if (level)
    backtrack_without_updating_phases (0);
  if (!constraint_cat) {
    constraint_cat = KITTEN_NAMESPACE (kitten_init ());
    size_t idx = 0;
    for (auto &other : assumptions)
      KITTEN_NAMESPACE (cat_unit_with_id (constraint_cat, -++idx, other));
  }
  if (lit) {
    constraint_tmp.push_back (lit);
    return;
  }
  assert (!lit);
  stats.constraints_added++;
  // id of the external constraint
  const int64_t ext_id = clause_id;
  LOG (constraint_tmp, "shrinking constraint");
  bool satisfied_constraint = false;
  bool derived_constraint = false;
  const vector<int>::const_iterator end = constraint_tmp.end ();
  vector<int>::iterator i = constraint_tmp.begin ();
  // use analyzed for tracking units with lrat
  assert (analyzed.empty ());
  for (vector<int>::const_iterator j = i; j != end; j++) {
    int tmp = marked (*j);
    if (tmp > 0) {
      derived_constraint = true;
      LOG ("removing duplicated literal %d from constraint", *j);
    } else if (tmp < 0) {
      LOG ("tautological since both %d and %d occur in constraint", -*j,
           *j);
      satisfied_constraint = true;
      break;
    } else {
      tmp = val (*j);
      if (tmp < 0) {
        if (lrat) {
          mark (*j);
          analyzed.push_back (*j);
          lrat_chain.push_back (unit_id (*j));
        }
        derived_constraint = true;
        LOG ("removing falsified literal %d from constraint clause", *j);
      } else if (tmp > 0) {
        LOG ("satisfied constraint with literal %d", *j);
        satisfied_constraint = true;
        break;
      } else {
        *i++ = *j;
        mark (*j);
      }
    }
  }
  constraint_tmp.resize (i - constraint_tmp.begin ());
  for (const auto &lit : constraint_tmp)
    unmark (lit);
  if (lrat)
    for (const auto &lit : analyzed)
      unmark (lit);
  analyzed.clear ();
  if (satisfied_constraint) {
    constraint_tmp.clear ();
    stats.constraints_sat++;
    return;
  }
  int64_t int_id = ext_id;
  if (derived_constraint) {
    int_id = ++clause_id;
    if (proof) {
      if (lrat)
        lrat_chain.push_back (ext_id);
      proof->add_assumption_clause (int_id, constraint_tmp, lrat_chain);
      lrat_chain.clear ();
    }
  }
  constraint_ids[ext_id] = int_id;
  if (constraint_tmp.empty ()) {
    constraints.push_back (0);
    unsat_constraint = true;
    constraint_fail[int_id] = 1;
    conclusion.push_back (int_id);
    conclusion.push_back (ext_id);
    // unsat_constraint already contains the information...
    // marked_failed = false; // allow to trigger failing ()
  } else {
    for (const auto lit : constraint_tmp) {
      constraints.push_back (lit);
      stats.constraints_lit++;
      Flags &f = flags (lit);
      if (!f.constrained) {
        constraint_vars.push_back (lit);
        f.constrained = true;
        freeze (lit);
      }
    }
    constraints.push_back (0);
  }
}

bool Internal::failed_constraint (int64_t id) {
  conclude_unsat ();
  if (unsat)
    return false;
  if (!unsat_constraint)
    return false;
  if (constraint_ids.find (id) == constraint_ids.end ())
    return false;
  assert (constraint_vars.size () == constraint_fail.size ());
  return constraint_fail[constraint_ids[id]];
}

void Internal::reset_constraint () {
  if (!constraints.empty ())
    stats.constraints_reset++;
  for (auto lit : constraints) {
    if (lit) {
      melt (lit);
      flags (lit).constrained = 0;
    }
  }
  LOG ("cleared %zd constraint literals", constraints.size ());
  constraints.clear ();
  constraint_vars.clear ();
  constraint_ids.clear ();
  constraint_fail.clear ();
  if (constraint_cat)
    KITTEN_NAMESPACE (kitten_release (constraint_cat));
  constraint_cat = 0;
  unsat_constraint = 0;
  marked_failed = true;
}

void Internal::analyze_failing_constraint (int lit) {
  stats.constraints_analyzed++;
  START (analyze);

  LOG ("analyzing failing constraint %d", lit);

  assert (analyzed.empty ());
  assert (clause.empty ());
  assert (lrat_chain.empty ());
  assert (!marked_failed);
  assert (!unsat);

  Var &v = var (lit);
  Flags &f = flags (lit);
  int failed_unit = 0;
  int failed_clashing = 0;
  int first_failed = 0;
  int failed_level = v.level;
  int efailed = externalize (lit);
  if (!failed_level)
    failed_unit = lit;
  else if (!v.reason && f.assumed)
    assert (false); // kitten should know
  else
    first_failed = lit;

  assert (clause.empty ());

  // Get the 'failed' assumption from one of the three cases.
  int failed;
  if (failed_unit)
    failed = failed_unit;
  else if (failed_clashing)
    failed = failed_clashing;
  else
    failed = first_failed;
  assert (failed);
  assert (efailed);

  // First case (1).
  if (failed_unit) {
    assert (failed == failed_unit);
    LOG ("root-level falsified constraint %d", failed);
    int64_t id = 0;
    if (lrat) {
      unsigned eidx = (efailed > 0) + 2u * (unsigned) abs (efailed);
      assert ((size_t) eidx < external->ext_units.size ());
      id = external->ext_units[eidx];
      if (!id) {
        id = unit_id (-failed_unit);
      }
      assert (id);
    }
    KITTEN_NAMESPACE (cat_unit_with_id (constraint_cat, id, -failed));
    goto DONE;
  }

  // Second case (2).
  if (failed_clashing) {
    assert (false);
    goto DONE;
  }

  // Fall through to third case (3).
  LOG ("starting with constraint %d falsified on minimum decision level "
       "%d",
       first_failed, failed_level);

  assert (first_failed);
  assert (failed_level > 0);

  // The 'analyzed' stack serves as working stack for a BFS through the
  // implication graph until decisions, which are all assumptions, or
  // units are reached.  This is simpler than corresponding code in
  // 'analyze'.
  {
    LOG ("failed assumption %d", first_failed);
    Flags &f = flags (first_failed);
    assert (!f.seen);
    f.seen = true;
    analyzed.push_back (-first_failed);
    clause.push_back (-first_failed);
  }

  {
    // no LRAT do bfs as it was before
    if (!lrat) {
      size_t next = 0;
      while (next < analyzed.size ()) {
        const int lit = analyzed[next++];
        assert (val (lit) > 0);
        Var &v = var (lit);
        if (!v.level)
          continue;
        if (v.reason == external_reason) {
          v.reason = learn_external_reason_clause (lit, 0, true);
          if (!v.reason) {
            v.level = 0;
            continue;
          }
        }
        assert (v.reason != external_reason);
        if (v.reason) {
          assert (v.level);
          LOG (v.reason, "analyze reason");
          for (const auto &other : *v.reason) {
            Flags &f = flags (other);
            if (f.seen)
              continue;
            f.seen = true;
            assert (val (other) < 0);
            analyzed.push_back (-other);
          }
        } else {
          assert (assumed (lit));
          LOG ("failed assumption %d", lit);
          clause.push_back (-lit);
        }
      }
      clear_analyzed_literals ();
    } else if (!unsat_constraint) { // LRAT for case (3)
      assert (clause.size () == 1);
      const int lit = clause[0];
      Var &v = var (lit);
      assert (v.reason);
      if (v.reason == external_reason) { // does this even happen?
        v.reason = learn_external_reason_clause (lit, 0, true);
      }
      assert (v.reason != external_reason);
      if (v.reason)
        assume_analyze_reason (lit, v.reason);
      else {
        int64_t id = unit_id (lit);
        lrat_chain.push_back (id);
      }
      clear_analyzed_literals ();
    } else { // TODO: LRAT for unsat_constraint
    }
    clear_analyzed_literals ();

    // Doing clause minimization here does not do anything because
    // the clause already contains only one literal of each level
    // and minimization can never reduce the number of levels

    VERBOSE (1, "found %zd failed assumptions %.0f%%", clause.size (),
             percent (clause.size (), assumptions.size ()));

    // We do not actually need to learn this clause, since the conflict is
    // forced already by some other clauses.  There is also no bumping
    // of variables nor clauses necessary.  But we still want to check
    // correctness of the claim that the determined subset of failing
    // assumptions are a high-level core or equivalently their negations
    // form a unit-implied clause.
    //
    if (!unsat_constraint) {
      external->check_learned_clause ();
      if (proof) {
        vector<int> eclause;
        for (auto &lit : clause)
          eclause.push_back (externalize (lit));
        proof->add_assumption_clause (++clause_id, eclause, lrat_chain);
        conclusion.push_back (clause_id);
      }
    } else {
      // TODO: unsat_constraint
    }
    lrat_chain.clear ();
    clause.clear ();
  }

DONE:

  STOP (analyze);
}

} // namespace CaDiCaL
