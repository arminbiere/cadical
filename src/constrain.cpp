#include "internal.hpp"

namespace CaDiCaL {

void Internal::constrain (int lit) {
  if (lit)
    constraint.push_back (lit);
  else {
    if (level)
      backtrack ();
    LOG (constraint, "shrinking constraint");
    bool satisfied_constraint = false;
    const vector<int>::const_iterator end = constraint.end ();
    vector<int>::iterator i = constraint.begin ();
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
    constraint.resize (i - constraint.begin ());
    for (const auto &lit : constraint)
      unmark (lit);
    if (satisfied_constraint)
      constraint.clear ();
    else if (constraint.empty ()) {
      unsat_constraint = true;
      if (!conflict_id)
        marked_failed = false; // allow to trigger failing ()
    } else
      for (const auto lit : constraint)
        freeze (lit);
  }
}

bool Internal::failed_constraint () { return unsat_constraint; }

void Internal::reset_constraint () {
  for (auto lit : constraint)
    melt (lit);
  LOG ("cleared %zd constraint literals", constraint.size ());
  constraint.clear ();
  unsat_constraint = false;
  marked_failed = true;
}

bool Internal::constraining () {
  return level == assumptions2.level () && constraint.size ();
}

int Internal::decide_constrain () {
  int res = 0;
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
      marked_failed = false;
      res = 20;
    }
  }

#ifndef NDEBUG
  for (auto lit : constraint)
    sum -= lit;
  assert (!sum); // Checksum of literal should not change!
#endif
  return res;
}

} // namespace CaDiCaL
