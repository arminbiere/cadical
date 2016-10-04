#ifndef _profiles_h_INCLUDED
#define _profiles_h_INCLUDED

namespace CaDiCaL {

// To profile say 'foo', just add another line 'PROFILE(foo)' and wrap
// the code to be profiled within a 'START (foo)' / 'STOP (foo)' block.

#define PROFILES \
PROFILE(analyze) \
PROFILE(bump) \
PROFILE(decide) \
PROFILE(minimize) \
PROFILE(parse) \
PROFILE(propagate) \
PROFILE(reduce) \
PROFILE(restart) \
PROFILE(search) \

struct Profiles {
#define PROFILE(NAME) \
  double NAME;
  PROFILES
#undef PROFILE
};

};

#endif
