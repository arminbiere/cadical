#include "internal.hpp"
#include "macros.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

void Internal::init_occs () {
  assert (!otab);
  NEW (otab, vector<Clause*>, 2*vsize);
}

size_t Internal::bytes_occs () {
  assert (occs ());
  size_t bytes = 0;
  for (int idx = 1; idx <= max_var; idx++)
    bytes += bytes_vector (occs (idx)),
    bytes += bytes_vector (occs (-idx));
  return bytes;
}

void Internal::reset_occs () {
  assert (otab);
  DEL (otab, vector<Clause*>, 2*vsize);
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
