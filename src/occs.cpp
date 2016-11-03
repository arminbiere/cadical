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

void Internal::init_noccs () {
  assert (!noccs);
  NEW (noccs, long, 2*max_var+1);
  noccs += max_var;
  for (int lit = -max_var; lit <= max_var; lit++) noccs[lit] = 0;
}

void Internal::reset_noccs () {
  assert (noccs);
  noccs -= max_var;
  DEL (noccs, long, 2*max_var+1);
  noccs = 0;
}

};
