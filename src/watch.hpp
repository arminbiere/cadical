#ifndef _watch_hpp_INCLUDED
#define _watch_hpp_INCLUDED

#ifndef NDEBUG
#include "clause.hpp"
#endif

namespace CaDiCaL {

class Clause;

struct Watch {
  int blit;             // if blocking literal is true do not visit clause
  int size;             // same as 'clause->size'
  Clause * clause;
  Watch (int b, Clause * c, int s) : blit (b), size (s), clause (c) {
    assert (b), assert (c), assert (c->size == s);
  }
  Watch () { }
};

typedef vector<Watch> Watches;          // of one literal

};

#endif
