#include "internal.hpp"

#include "macros.hpp"

namespace CaDiCaL {

int Internal::next_decision_variable () {
  long searched = 0;
  int res;
  while (val (res = var2idx (queue.bassigned)))
    queue.bassigned = queue.bassigned->prev, searched++;
  if (searched) {
    stats.searched += searched;
    queue.bumped = btab[var2idx (queue.bassigned)];
  }
  LOG ("next VMTF decision variable %d", res);
  return res;
}

void Internal::decide () {
  START (decide);
  level++;
  stats.decisions++;
  int idx = next_decision_variable ();
  int decision = phases[idx] * idx;
  control.push_back (Level (decision));
  LOG ("decide %d", decision);
  assign (decision);
  STOP (decide);
}

};
