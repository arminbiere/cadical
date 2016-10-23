#include "internal.hpp"
#include "macros.hpp"

namespace CaDiCaL {

int Internal::next_decision_variable () {
  long searched = 0;
  int res = queue.bassigned;
  while (val (res))
    res = link (res).prev, searched++;
  if (searched) {
    stats.searched += searched;
    queue.bassigned = res;
    queue.bumped = btab[queue.bassigned];
    LOG ("queue assigned now %d bumped %ld", queue.bassigned, queue.bumped);
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
