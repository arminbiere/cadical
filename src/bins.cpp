#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Binary implication graph lists.

void Internal::init_bins () {
  assert (big.empty ());
  while (big.size () < 2*vsize)
    big.push_back (Bins ());
  LOG ("initialized binary implication graph");
}

void Internal::reset_bins () {
  assert (!big.empty ());
  erase_vector (big);
  LOG ("reset binary implication graph");
}

}
