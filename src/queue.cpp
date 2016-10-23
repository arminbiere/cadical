#include "internal.hpp"
#include "iterator.hpp"

namespace CaDiCaL {

void Queue::init (Internal * internal, int new_max_var) {
  int prev = last;
  assert ((size_t) new_max_var < internal->vsize);
  for (int i = new_max_var; i > internal->max_var; i--) {
    Link * l = internal->ltab + i;
    if ((l->prev = prev)) internal->ltab[prev].next = i; else first = i;
    internal->btab[i] = ++internal->stats.bumped;
    prev = i;
  }
  if (prev) internal->ltab[prev].next = 0; else first = 0;
  bumped = internal->btab[prev];
  last = bassigned = prev;
}

void Queue::save (Internal * internal, vector<int> & order) {
  assert (order.empty ());
  order.reserve (internal->max_var);
  for (int idx = first; idx; idx = internal->ltab[idx].next)
    order.push_back (idx);
  assert (order.size () == (size_t) internal->max_var);
}

void Queue::restore (Internal * internal, const vector<int> & order) {
  int prev = 0;
  for (const_int_iterator i = order.begin (); i != order.end (); i++) {
    const int idx = *i;
    Link * l = &internal->ltab[idx];
    if ((l->prev = prev)) {
      assert (internal->bumped (prev) < internal->bumped (idx));
      internal->ltab[prev].next = idx;
    } else first = idx;
    prev = idx;
  }
  if (prev) internal->ltab[prev].next = 0; else first = 0;
  last = bassigned = prev;
  bumped = internal->btab[prev];
}

};
