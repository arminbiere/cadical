#include "internal.hpp"

namespace CaDiCaL {

void Queue::init (Internal * internal, int new_max_var) {
  Var * prev = 0;
  for (int i = new_max_var; i > internal->max_var; i--) {
    Var * v = &internal->var (i);
    if ((v->prev = prev)) prev->next = v;
    else first = v;
    v->bumped = ++internal->stats.bumped;
    prev = v;
  }
  if (prev) prev->next = 0; else first = 0;
  last = assigned = prev;
}

void Queue::save (Internal * internal, vector<int> & order) {
  for (Var * v = first; v; v = v->next)
    order.push_back (internal->var2idx (v));
}

void Queue::restore (Internal * internal, const vector<int> & order) {
  Var * prev = 0;
  for (size_t i = 0; i < order.size (); i++) {
    const int idx = order[i];
    Var * v = &internal->var (idx);
    if ((v->prev = prev)) {
      assert (prev->bumped < v->bumped);
      prev->next = v;
    } else first = v;
    prev = v;
  }
  if (prev) prev->next = 0; else first = 0;
  last = assigned = prev;
}

};
