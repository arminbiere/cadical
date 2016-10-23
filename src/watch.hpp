#ifndef _watch_hpp_INCLUDED
#define _watch_hpp_INCLUDED

#ifndef NDEBUG
#include "clause.hpp"
#endif

namespace CaDiCaL {

class Clause;

struct Watch {
  int blit;             // if blocking literal is true do not visit clause
  int size;             // size of clause
  Clause * clause;
  Watch (int b, Clause * c, int size) :
    blit (b), size (size), clause (c)
  {
    assert (c->size == size);
  }
  Watch () { }
};

typedef vector<Watch> Watches;          // of one literal

};

#endif
