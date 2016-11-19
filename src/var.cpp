#include "internal.hpp"

#include <cstring>

namespace CaDiCaL {

void Internal::reset_removed () {
  memset (rtab, 0, max_var + 1);
}

void Internal::reset_added () {
  memset (atab, 0, max_var + 1);
}

};
