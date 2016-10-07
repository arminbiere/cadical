#include "solver.hpp"

namespace CaDiCaL {

int Solver::next_decision_variable () {
  int res;
  while (val (res = var2idx (queue.assigned)))
    queue.assigned = queue.assigned->prev, stats.searched++;
  LOG ("next VMTF decision variable %d", res);
  return res;
}

void Solver::decide () {
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
