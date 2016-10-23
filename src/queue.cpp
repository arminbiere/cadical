#include "internal.hpp"
#include "iterator.hpp"

namespace CaDiCaL {

void Queue::init (Internal * internal, int new_max_var) {
  Var * prev = last;
  assert ((size_t) new_max_var < internal->vsize);
  for (int i = new_max_var; i > internal->max_var; i--) {
    Var * v = internal->vtab + i;
    if ((v->prev = prev)) prev->next = v; else first = v;
    internal->btab[i] = ++internal->stats.bumped;
    prev = v;
  }
  if (prev) prev->next = 0; else first = 0;
  bumped = internal->btab[prev ? prev - internal->vtab : 0];
  last = bassigned = prev;
}

void Queue::save (Internal * internal, vector<int> & order) {
  assert (order.empty ());
  order.reserve (internal->max_var);
  for (Var * v = first; v; v = v->next)
    order.push_back (internal->var2idx (v));
  assert (order.size () == (size_t) internal->max_var);
}

void Queue::restore (Internal * internal, const vector<int> & order) {
  Var * prev = 0;
  for (const_int_iterator i = order.begin (); i != order.end (); i++) {
    const int idx = *i;
    Var * v = &internal->var (idx);
    if ((v->prev = prev)) {
      assert (internal->bumped (internal->var2idx (prev)) <
              internal->bumped (internal->var2idx (v)));
      prev->next = v;
    } else first = v;
    prev = v;
  }
  if (prev) prev->next = 0; else first = 0;
  last = bassigned = prev;
  bumped = internal->btab[prev ? prev - internal->vtab : 0];
}

};
