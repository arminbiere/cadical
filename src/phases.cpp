#include "internal.hpp"

namespace CaDiCaL {

void Internal::copy_phases (vector<Phase> & dst) {
  START (copy);
  for (int i = 1; i <= max_var; i++)
    dst[i] = vals[i];
  STOP (copy);
}

void Internal::clear_phases (vector<Phase> & dst) {
  START (copy);
  for (int i = 1; i <= max_var; i++)
    dst[i] = 0;
  STOP (copy);
}

}
