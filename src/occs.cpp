#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Occurrence lists.

void Internal::init_occs () {
  assert (!otab);
  NEW_ZERO (otab, Occs, 2*vsize);
  LOG ("initialized occurrence lists");
}

void Internal::reset_occs () {
  assert (otab);
  RELEASE_DELETE (otab, Occs, 2*vsize);
  LOG ("reset occurrence lists");
  otab = 0;
}

/*------------------------------------------------------------------------*/

// One-sided occurrence counter (each literal has its own counter).

void Internal::init_noccs () {
  assert (!ntab);
  NEW_ZERO (ntab, long, 2*vsize);
  LOG ("initialized two-sided occurrence counters");
}

void Internal::reset_noccs () {
  assert (ntab);
  DELETE_ONLY (ntab, long, 2*vsize);
  LOG ("reset two-sided occurrence counters");
  ntab = 0;
}

}
