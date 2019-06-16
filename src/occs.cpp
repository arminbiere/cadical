#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Occurrence lists.

void Internal::init_occs () {
  while (otab.size () < 2*vsize)
    otab.push_back (Occs ());
  LOG ("initialized occurrence lists");
}

void Internal::reset_occs () {
  assert (occurring ());
  erase_vector (otab);
  LOG ("reset occurrence lists");
}

/*------------------------------------------------------------------------*/

// One-sided occurrence counter (each literal has its own counter).

void Internal::init_noccs () {
  assert (ntab.empty ());
  while (ntab.size () < 2*vsize)
    ntab.push_back (0);
  LOG ("initialized two-sided occurrence counters");
}

void Internal::reset_noccs () {
  assert (!ntab.empty ());
  erase_vector (ntab);
  LOG ("reset two-sided occurrence counters");
}

}
