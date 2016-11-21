#ifndef _watch_hpp_INCLUDED
#define _watch_hpp_INCLUDED

#include "clause.hpp"

#include <cassert>
#include <vector>

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

inline void shrink_watches (Watches & ws) { shrink_vector (ws); }

typedef Watches::iterator watch_iterator;
typedef Watches::const_iterator const_watch_iterator;

};


#endif
