#ifdef PROFILE_MODE

#include "internal.hpp"

namespace CaDiCaL {

bool Internal::propagate_stable () {
  assert (stable);
  PROFILE_SCOPE (propstable);
  return propagate ();
}

void Internal::analyze_stable () {
  assert (stable);
  PROFILE_SCOPE (analyzestable);
  analyze ();
}

int Internal::decide_stable () {
  assert (stable);
  return decide ();
}

}; // namespace CaDiCaL

#else
int stable_if_not_profile_mode_dummy;
#endif
