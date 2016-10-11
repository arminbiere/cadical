#include "internal.hpp"

namespace CaDiCaL {

void Queue::init (Internal * internal) {
  Var * prev = 0;
  for (int i = internal->max_var; i; i--) {
    Var * v = &internal->var (i);
    if ((v->prev = prev)) prev->next = v;
    else first = v;
    v->bumped = ++internal->stats.bumped;
    prev = v;
  }
  last = assigned = prev;
}

};
