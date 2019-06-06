#include "internal.hpp"

namespace CaDiCaL {

void Internal::copy_phases (Phase * & dst) {
  assert (sizeof (Phase) == 1);
  memcpy (dst, vals, max_var + 1);
}

void Internal::clear_phases (Phase * & dst) {
  assert (sizeof (Phase) == 1);
  memset (dst, 0, max_var + 1);
}

}
