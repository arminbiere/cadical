#ifndef _watch_hpp_INCLUDED
#define _watch_hpp_INCLUDED

#ifndef NDEBUG
#include "clause.hpp"
#endif

namespace CaDiCaL {

class Clause;

struct Watch {
  int blit;             // if blocking literal is true do not visit clause
  bool binary;
  Clause * clause;
  Watch (int b, bool bin, Clause * c) : blit (b), binary (bin), clause (c) {
    assert (binary == (c->size == 2));
  }
  Watch () { }
};

typedef vector<Watch> Watches;          // of one literal

};

#endif
