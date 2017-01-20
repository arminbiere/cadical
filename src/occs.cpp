#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Occurrence lists.

void Internal::init_occs () {
  assert (!otab);
  NEW (otab, Occs, 2*vsize);
}

void Internal::reset_occs () {
  assert (otab);
  DEL (otab, Occs, 2*vsize);
  otab = 0;
}

/*------------------------------------------------------------------------*/

// One-sided occurrence counter (each literal has its own counter).

void Internal::init_noccs () {
  assert (!ntab);
  NEW (ntab, long, 2*vsize);
  ZERO (ntab, long, 2*vsize);
}

void Internal::reset_noccs () {
  assert (ntab);
  DEL (ntab, long, 2*vsize);
  ntab = 0;
}

/*------------------------------------------------------------------------*/

// Two-sided occurrence counter (each variable has one counter).

void Internal::init_noccs2 () {
  assert (!ntab2);
  NEW (ntab2, long, vsize);
  ZERO (ntab2, long, vsize);
}

void Internal::reset_noccs2 () {
  assert (ntab2);
  DEL (ntab2, long, vsize);
  ntab2 = 0;
}

};
