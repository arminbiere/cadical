#ifndef _watch_hpp_INCLUDED
#define _watch_hpp_INCLUDED


#include <cassert>
#include <vector>

namespace CaDiCaL {

// Watch lists for CDCL search.  The blocking literal (see also comments
// related to 'propagate') is a must and thus combining that with a 64 bit
// pointer will give a 16 byte (8 byte aligned) structure anyhow, which
// means the additional 4 bytes for abstracting the size and redundancy come
// for free.  As alternative one could use a 32-bit reference instead of the
// pointer which would however limit the number of clauses to '2^32 - 1'.
// One would also need to use at least one more bit (either taken away from
// the variable space or the clauses) to denote whether the watch is binary.

class Clause;

struct Watch {

  Clause * clause;
  signed int blit;
  bool redundant;
  bool binary;

  Watch (int b, Clause * c) :
    clause (c), blit (b), redundant (c->redundant), binary (c->size == 2)
  { }

  Watch () { }
};

typedef vector<Watch> Watches;          // of one literal

inline void shrink_watches (Watches & ws) { shrink_vector (ws); }

typedef Watches::iterator watch_iterator;
typedef Watches::const_iterator const_watch_iterator;

};

#endif
