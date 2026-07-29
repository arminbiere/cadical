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
  if (satisfied_constraint) {
    constraint_tmp.clear ();
    stats.constraints_sat++;
    return;
  }
  int64_t int_id = ext_id;
  if (derived_constraint) {
    int_id = ++clause_id;
    if (proof) {
      // TODO: lrat
      proof->add_assumption_clause (int_id, constraint_tmp, lrat_chain);
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
  // TODO:
  assert (false);
}

} // namespace CaDiCaL
