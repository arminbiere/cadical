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
  stats.constraints_added++;
  LOG (constraint_tmp, "shrinking constraint");
  bool satisfied_constraint = false;
  const vector<int>::const_iterator end = constraint_tmp.end ();
  vector<int>::iterator i = constraint_tmp.begin ();
  for (vector<int>::const_iterator j = i; j != end; j++) {
    int tmp = marked (*j);
    if (tmp > 0) {
      LOG ("removing duplicated literal %d from constraint", *j);
    } else if (tmp < 0) {
      LOG ("tautological since both %d and %d occur in constraint", -*j,
           *j);
      satisfied_constraint = true;
      break;
    } else {
      tmp = val (*j);
      if (tmp < 0) {
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
  if (constraint_tmp.empty ()) {
    constraints.push_back (0);
    unsat_constraint = true;
    if (!unsat)
      marked_failed = false; // allow to trigger failing ()
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

bool Internal::failed_constraint (size_t idx) {
  if (unsat) {
    assert (!unsat_constraint);
    return false;
  }
  if (!marked_failed) {
    failing ();
    marked_failed = true;
  }
  conclude_unsat ();
  return unsat_constraint;
}

void Internal::reset_constraint () {
  if (!constraints.empty ())
    stats.constraints_reset++;
  for (auto lit : constraints) {
    if (lit)
      melt (lit);
    flags (lit).constrained = 0;
  }
  LOG ("cleared %zd constraint literals", constraint.size ());
  constraints.clear ();
  constraint_vars.clear ();
  constraint_idx.clear ();
  KITTEN_NAMESPACE (kitten_release (constraint_cat));
  constraint_cat = 0;
  unsat_constraint = false;
  marked_failed = true;
}

} // namespace CaDiCaL
