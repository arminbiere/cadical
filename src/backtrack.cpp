#include "internal.hpp"

namespace CaDiCaL {

// The global assignment stack can only be (partially) reset through
// 'backtrack' which is the only function using 'unassign' (inlined and thus
// local to this file).

inline void Internal::search_unassign (int lit) {
  assert (!simplifying);
  assert (val (lit) > 0);
  int idx = vidx (lit);
  vals[idx] = 0;
  vals[-idx] = 0;
  LOG ("unassign %d", lit);
  if (queue.bumped < btab[idx]) update_queue_unassigned (idx);
}

void Internal::backtrack (int target_level) {
  assert (!simplifying);
  assert (target_level <= level);
  if (target_level == level) return;
  LOG ("backtracking to decision level %d", target_level);
  int decision = control[target_level + 1].decision, lit;
  do {
    assert (!trail.empty ());
    search_unassign (lit = trail.back ());
    trail.pop_back ();
  } while (lit != decision);
  if (trail.size () < propagated) propagated = trail.size ();
  control.resize (target_level + 1);
  level = target_level;
}

};
