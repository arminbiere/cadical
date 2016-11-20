#include "internal.hpp"

#include <cstring>

namespace CaDiCaL {

void Internal::reset_removed () {
  LOG ("marking all variables as not removed");
  for (int idx = 1; idx <= max_var; idx++)
    flags (idx).removed = false;
}

void Internal::reset_added () {
  LOG ("marking all variables as not added");
  for (int idx = 1; idx <= max_var; idx++)
    flags (idx).added = false;
}

};
