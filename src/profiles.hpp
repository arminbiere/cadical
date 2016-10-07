#ifndef _profiles_h_INCLUDED
#define _profiles_h_INCLUDED

namespace CaDiCaL {

class Solver;

// To profile say 'foo', just add another line 'PROFILE(foo)' and wrap
// the code to be profiled within a 'START (foo)' / 'STOP (foo)' block.

#define PROFILES \
PROFILE(analyze,3) \
PROFILE(bump,4) \
PROFILE(decide,3) \
PROFILE(minimize,4) \
PROFILE(parse,1) \
PROFILE(propagate,4) \
PROFILE(reduce,2) \
PROFILE(restart,2) \
PROFILE(search,1) \

struct Profile {
  double value;
  const char * name;
  int level;
  Profile (const char * n, int l) : name (n), level (l) { }
};

struct Profiles {
  Solver * solver;
#define PROFILE(NAME, LEVEL) \
  Profile NAME;
  PROFILES
#undef PROFILE
  Profiles (Solver *);
};

};

#endif
