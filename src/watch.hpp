#ifndef _watch_hpp_INCLUDED
#define _watch_hpp_INCLUDED

#include "clause.hpp"
#include "cector.hpp"

#include <cassert>

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

};

namespace CaDiCaL {

#if 0
typedef vector<Watch> Watches;          // of one literal
inline void shrink_watches (Watches & ws) { shrink_vector (ws); }
#else
typedef cector<Watch> Watches;
inline void shrink_watches (Watches & ws) { ws.shrink (); }
#endif

typedef Watches::iterator watch_iterator;
typedef Watches::const_iterator const_watch_iterator;

};


#endif
