#include "internal.hpp"
#include "macros.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

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

};
