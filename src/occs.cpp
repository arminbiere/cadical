#include "internal.hpp"
#include "macros.hpp"

namespace CaDiCaL {

void Internal::init_occs () {
  assert (!occs);
  NEW (occs, vector<Clause*>, 2*max_var+1);
  occs += max_var;
}

void Internal::account_occs () {
  size_t bytes = 0;
  for (int lit = -max_var; lit <= max_var; lit++)
    bytes += VECTOR_BYTES (occs[lit]);
  inc_bytes (bytes);
  dec_bytes (bytes);
}

void Internal::reset_occs () {
  assert (occs);
  occs -= max_var;
  DEL (occs, vector<Clause*>, 2*max_var+1);
  occs = 0;
}

};
