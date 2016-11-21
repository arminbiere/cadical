#ifndef _watch_hpp_INCLUDED
#define _watch_hpp_INCLUDED

#ifndef NDEBUG
#include "clause.hpp"
#endif

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

#if 1

namespace CaDiCaL {

typedef vector<Watch> Watches;          // of one literal

inline void shrink_watches (Watches & ws) { shrink_vector (ws); }

typedef vector<Watch>::iterator watch_iterator;
typedef vector<Watch>::const_iterator const_watch_iterator;

};

#else

#include "cector.hpp"

namespace CaDiCaL {

#define WATCHES

typedef cector<Watch> Watches;
typedef Watches::iterator watch_iterator;
typedef Watches::const_iterator const_watch_iterator;

inline void shrink_watches (Watches & ws) { ws.shrink (); }

};

#endif

#endif
