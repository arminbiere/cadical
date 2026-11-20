#ifdef PROFILE_MODE
#include "internal.hpp"

namespace CaDiCaL {

bool Internal::propagate_unstable () {
  assert (!stable);
  PROFILE_SCOPE (propunstable);
  return propagate ();
}

void Internal::analyze_unstable () {
  assert (!stable);
  PROFILE_SCOPE (analyzeunstable);
  analyze ();
}

int Internal::decide_unstable () {
  assert (!stable);
  return decide ();
}

}; // namespace CaDiCaL
#else
int unstable_if_no_profile_mode;
#endif
