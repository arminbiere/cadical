#include "internal.hpp"

namespace CaDiCaL {

// This function determines the next decision variable, without actually
// removing it from the decision queue, e.g., calling it multiple times
// without any assignment will return the same result.  This is of course
// used below in 'decide' but also in 'reuse_trail' to determine the largest
// decision level to backtrack to during 'restart' without changing the
// assigned variables.

int Internal::next_decision_variable () {
  long searched = 0;
  int res = queue.unassigned;
  while (val (res))
    res = link (res).prev, searched++;
  if (searched) {
    stats.searched += searched;
    update_queue_unassigned (res);
  }
  LOG ("next decision variable %d", res);
  return res;
}

// Just assume the given literal as decision (increase decision level and
// assign it).  This is used below in 'decide' and in failed literal
// probing to assign the next 'probe'.

void Internal::assume_decision (int lit) {
  level++;
  control.push_back (Level (lit));
  LOG ("decide %d", lit);
  assign_decision (lit);
}

// Search for the next decision and assign it to the saved phase.  Requires
// that not all variables are assigned.

void Internal::decide () {
  START (decide);
  stats.decisions++;
  int idx = next_decision_variable ();
  int decision = phases[idx] * idx;
  assume_decision (decision);
  STOP (decide);
}

};
