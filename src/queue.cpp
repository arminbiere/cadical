#include "internal.hpp"
#include "iterator.hpp"

namespace CaDiCaL {

void Queue::init (Internal * internal, int new_max_var) {
  Link * prev = last;
  assert ((size_t) new_max_var < internal->vsize);
  for (int i = new_max_var; i > internal->max_var; i--) {
    Link * l = internal->ltab + i;
    if ((l->prev = prev)) prev->next = l; else first = l;
    internal->btab[i] = ++internal->stats.bumped;
    prev = l;
  }
  if (prev) prev->next = 0; else first = 0;
  bumped = internal->btab[prev ? prev - internal->ltab : 0];
  last = bassigned = prev;
}

void Queue::save (Internal * internal, vector<int> & order) {
  assert (order.empty ());
  order.reserve (internal->max_var);
  for (Link * l = first; l; l = l->next)
    order.push_back (internal->link2idx (l));
  assert (order.size () == (size_t) internal->max_var);
}

void Queue::restore (Internal * internal, const vector<int> & order) {
  Link * prev = 0;
  for (const_int_iterator i = order.begin (); i != order.end (); i++) {
    const int idx = *i;
    Link * l = &internal->link (idx);
    if ((l->prev = prev)) {
      assert (internal->bumped (internal->link2idx (prev)) <
              internal->bumped (internal->link2idx (l)));
      prev->next = l;
    } else first = l;
    prev = l;
  }
  if (prev) prev->next = 0; else first = 0;
  last = bassigned = prev;
  bumped = internal->btab[prev ? prev - internal->ltab : 0];
}

};
