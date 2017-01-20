#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Binary implication graph lists.

void Internal::init_bins () {
  assert (!big);
  NEW (big, Bins, 2*vsize);
}

void Internal::reset_bins () {
  assert (big);
  DELETE (big, Bins, 2*vsize);
  big = 0;
}

};
