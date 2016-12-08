#include "internal.hpp"

namespace CaDiCaL {

// The specialized probing versions of 'unassign' and 'backtrack'.
// Difference is no need to update decision queue, nor control stack.

inline void Internal::probe_unassign (int lit) {
  assert (simplifying);
  assert (val (lit) > 0);
  int idx = vidx (lit);
  vals[idx] = 0;
  vals[-idx] = 0;
  LOG ("unassign %d", lit);
}

void Internal::packtrack (int probe) {
  assert (simplifying);
  assert (level == 1);
  LOG ("backtracking to root");
  int lit;
  do {
    assert (!trail.empty ());
    probe_unassign (lit = trail.back ());
    trail.pop_back ();
  } while (lit != probe);
  if (probagated > trail.size ()) probagated = trail.size ();
  if (probagated2 > trail.size ()) probagated2 = trail.size ();
  level = 0;
}

};
