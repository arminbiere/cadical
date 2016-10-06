#include "solver.hpp"

namespace CaDiCaL {

void Queue::init (Solver * solver) {
  Var * prev = 0;
  for (int i = solver->max_var; i; i--) {
    Var * v = &solver->vars[i];
    if ((v->prev = prev)) prev->next = v;
    else first = v;
    v->bumped = ++solver->stats.bumped;
    prev = v;
  }
  last = assigned = prev;
}

};
