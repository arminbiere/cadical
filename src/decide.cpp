#include "internal.hpp"
#include "macros.hpp"

namespace CaDiCaL {

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

void Internal::assume_decision (int lit) {
  level++;
  control.push_back (Level (lit));
  LOG ("decide %d", lit);
  assign (lit);
}

void Internal::decide () {
  START (decide);
  stats.decisions++;
  int idx = next_decision_variable ();
  int decision = phases[idx] * idx;
  assume_decision (decision);
  STOP (decide);
}

};
