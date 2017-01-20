#include "internal.hpp"

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

void Internal::check_var_stats () {
#ifndef NDEBUG
  int fixed = 0, eliminated = 0, substituted = 0;
  for (int idx = 1; idx <= max_var; idx++) {
    Flags & f = flags (idx);
    if (f.active ()) continue;
    if (f.fixed ()) fixed++;
    if (f.eliminated ()) eliminated++;
    if (f.substituted ()) substituted++;
  }
  assert (stats.now.fixed == fixed);
  assert (stats.now.eliminated == eliminated);
  assert (stats.now.substituted == substituted);
#endif
}

};
