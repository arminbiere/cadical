#ifdef PROFILE_MODE

#include "internal.hpp"

namespace CaDiCaL {

bool Internal::propagate_stable () {
  Assert (stable);
  START (propstable);
  bool res = propagate ();
  STOP (propstable);
  return res;
}

void Internal::analyze_stable () {
  Assert (stable);
  START (analyzestable);
  analyze ();
  STOP (analyzestable);
}

int Internal::decide_stable () {
  Assert (stable);
  return decide ();
}

}; // namespace CaDiCaL

#else
int stable_if_not_profile_mode_dummy;
#endif
