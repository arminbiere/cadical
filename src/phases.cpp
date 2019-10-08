#include "internal.hpp"

namespace CaDiCaL {

void Internal::copy_phases (vector<signed char> & dst) {
  START (copy);
  for (int i = 1; i <= max_var; i++)
    dst[i] = vals[i];
  STOP (copy);
}

void Internal::clear_phases (vector<signed char> & dst) {
  START (copy);
  for (int i = 1; i <= max_var; i++)
    dst[i] = 0;
  STOP (copy);
}

}
