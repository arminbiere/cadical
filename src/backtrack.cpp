#include "internal.hpp"

namespace CaDiCaL {

void Internal::unassign (int lit) {
  assert (val (lit) > 0);
  int idx = vidx (lit);
  vals[idx] = 0;
  vals[-idx] = 0;
  LOG ("unassign %d", lit);
  long b = btab[idx];
  if (queue.bumped >= b) return;
  queue.bassigned = ltab + idx;
  queue.bumped = b;
  LOG ("queue next moved to %d", idx);
}

void Internal::backtrack (int target_level) {
  assert (target_level <= level);
  if (target_level == level) return;
  LOG ("backtracking to decision level %d", target_level);
  int decision = control[target_level + 1].decision, lit;
  do {
    unassign (lit = trail.back ());
    trail.pop_back ();
  } while (lit != decision);
  if (trail.size () < propagated) propagated = trail.size ();
  control.resize (target_level + 1);
  level = target_level;
}

};
