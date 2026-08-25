#include "internal.hpp"
#include "kitten.h"
#include "profile.hpp"
#include <algorithm>
#include <cstdint>

namespace CaDiCaL {

extern "C" {
static int cat_terminate (void *data) {
  return ((Internal *) data)->terminated_asynchronously ();
}
}

void Internal::init_constraint_cat () {
  assert (!constraint_cat);
  constraint_cat = KITTEN_NAMESPACE (kitten_init ());
#ifdef LOGGING
  if (opts.log)
    KITTEN_NAMESPACE (kitten_set_logging) (constraint_cat);
#endif
  if (external->terminator)
    KITTEN_NAMESPACE (kitten_set_terminator) (constraint_cat, internal,
                                              cat_terminate);
  KITTEN_NAMESPACE (kitten_track_antecedents) (constraint_cat);
  KITTEN_NAMESPACE (kitten_keep_assumptions) (constraint_cat);
  // size_t idx = 0;
  for (auto &other : assumptions)
    KITTEN_NAMESPACE (kitten_assume_signed (constraint_cat, other));
}

void Internal::constrain (int lit) {
  if (unsat)
    return;
  if (level)
    backtrack_without_updating_phases (0);
  if (!constraint_cat)
    init_constraint_cat ();
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
          lrat_chain.push_back (unit_id (-*j));
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
    lrat_chain.clear ();
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
      proof->add_constraint_clause (int_id, constraint_tmp, lrat_chain,
                                    false);
      lrat_chain.clear ();
    }
  }
  // TODO: relies on int_id < INT_MAX. This is a hard limit for kitten,
  // but mapping the ids again, before adding them to kitten would get
  // rid of the dependence on the 'clause_id' counter and would allow
  // adding INT_MAX constraints per query (instead of INT_MAX - clause_id).
  assert (int_id < INT_MAX);
  constraint_ids[ext_id] = int_id;
  if (constraint_tmp.empty ()) {
    constraints.push_back (0);
    unsat_constraint = true;
    constraint_fail[int_id] = 1;
    conclusion.push_back (ext_id);
    if (int_id != ext_id)
      conclusion.push_back (int_id);
    LOG (conclusion, "empty constraint conclusion");
    // unsat_constraint already contains the information...
    // marked_failed = false; // allow to trigger failing ()
  } else {
    for (const auto lit : constraint_tmp) {
      constraints.push_back (lit);
      stats.constraints_lit++;
      Flags &f = flags (lit);
      if (!f.constrained) {
        constraint_vars.push_back (abs (lit));
        stats.constraints_vars++;
        f.constrained = true;
        freeze (lit);
        if (!f.assumed)
          constraints_without_assumptions++;
      }
    }
    KITTEN_NAMESPACE (cat_clause_with_id) (constraint_cat, int_id,
                                           constraint_tmp.size (),
                                           constraint_tmp.data ());
    constraints.push_back (0);
    constraint_tmp.clear ();
  }
}

void Internal::mark_failed_constraint (int64_t id) {
  constraint_fail[id] = true;
  // TODO: external id?
  conclusion.push_back (id);
}

bool Internal::failed_constraint (int64_t id) {
  conclude_unsat ();
  if (unsat)
    return false;
  if (!unsat_constraint)
    return false;
  if (constraint_ids.find (id) == constraint_ids.end ())
    return false;
  // assert (constraint_vars.size () == constraint_fail.size ());
  const bool res = constraint_fail[constraint_ids[id]];
  LOG ("%s constraint[%" PRId64 "]", res ? "failing" : "not failing", id);
  return res;
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
  constraints_without_assumptions = 0;
  constraint_cat = 0;
  unsat_constraint = 0;
  marked_failed = true;
}

void Internal::analyze_failing_constraint (int failed) {
  stats.constraints_analyzed++;
  PROFILE_SCOPE (analyze);

  LOG ("analyzing failing constraint %s", LOGLIT (failed));

  assert (analyzed.empty ());
  assert (clause.empty ());
  assert (lrat_chain.empty ());
  assert (!unsat);

  assert (val (failed) < 0);

  Var &w = var (failed);
  Flags &g = flags (failed);
  int efailed = externalize (failed);
  assert (w.reason || !w.level);

  assert (clause.empty ());

  if (w.reason == external_reason) {
    w.reason = learn_external_reason_clause (failed, 0, true);
    if (!w.reason) {
      // TODO: cover this
      assert (!w.level);
      w.level = 0;
    }
  }
  // unit.
  if (!w.level) {
    LOG ("root-level falsified constraint literal %d", failed);
    const int64_t id = ++clause_id;
    if (lrat) {
      unsigned eidx = (efailed > 0) + 2u * (unsigned) abs (efailed);
      assert ((size_t) eidx < external->ext_units.size ());
      int64_t uid = external->ext_units[eidx];
      if (!uid) {
        uid = unit_id (-failed);
      }
      lrat_chain.push_back (uid);
    }

    if (proof) // assumption clauses do not use constraints
      proof->add_assumption_clause (id, -failed, lrat_chain, false);
    lrat_chain.clear ();

    KITTEN_NAMESPACE (cat_unit_with_id (constraint_cat, id, -failed));
    return;
  }

  // Fall through to third case (3).
  LOG ("starting with constraint literal %s", LOGLIT (failed));

  // The 'trail' serves as working stack for a DFS through the
  // implication graph until decisions, which are all assumptions, or
  // units are reached.
  {
    LOG ("failed constraint literal %d", failed);
    assert (!g.seen);
    g.seen = true;
    analyzed.push_back (-failed);
    clause.push_back (-failed);
    assert (w.reason);
    assert (w.reason != external_reason);
    for (const auto &other : *w.reason) {
      Flags &f = flags (other);
      if (f.seen)
        continue;
      f.seen = true;
      assert (val (other) < 0);
      analyzed.push_back (-other);
    }
    if (lrat)
      lrat_chain.push_back (w.reason->id);
  }

  {
    size_t next = var (failed).trail;
    while (next != 0) {
      const int lit = trail[--next];
      Flags &f = flags (lit);
      if (!f.seen)
        continue;
      assert (val (lit) > 0);
      Var &v = var (lit);
      if (!v.level) {
        if (lrat) {
          lrat_chain.push_back (unit_id (lit));
        }
        continue;
      }
      if (v.reason == external_reason) {
        v.reason = learn_external_reason_clause (lit, 0, true);
        if (!v.reason) {
          assert (!v.level);
          v.level = 0;
          if (lrat) {
            lrat_chain.push_back (unit_id (lit));
          }
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
        if (lrat)
          lrat_chain.push_back (v.reason->id);
      } else {
        assert (assumed (lit) || constrained (lit));
        LOG ("failed assumption %d", lit);
        clause.push_back (-lit);
      }
    }
    clear_analyzed_literals ();

    // Doing clause minimization here does not do anything because
    // the clause already contains only one literal of each level
    // and minimization can never reduce the number of levels

    VERBOSE (1, "found %zd failed assumptions %.0f%%", clause.size (),
             percent (clause.size (),
                      assumptions.size () + constraint_vars.size ()));

    // We do not actually need to learn this clause, since the conflict is
    // forced already by some other clauses.  There is also no bumping
    // of variables nor clauses necessary.  But we still want to check
    // correctness of the claim that the determined subset of failing
    // assumptions are a high-level core or equivalently their negations
    // form a unit-implied clause. Finally add the clause to kitten.
    //
    const int64_t id = ++clause_id;
    if (proof) {
      std::reverse (lrat_chain.begin (), lrat_chain.end ());
      // not using constraints
      proof->add_assumption_clause (id, clause, lrat_chain, false);
    }
    KITTEN_NAMESPACE (cat_clause_with_id) (constraint_cat, id,
                                           clause.size (), clause.data ());
    lrat_chain.clear ();
    clause.clear ();
  }
}

} // namespace CaDiCaL
