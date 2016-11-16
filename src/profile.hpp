#ifndef _profiles_h_INCLUDED
#define _profiles_h_INCLUDED

namespace CaDiCaL {

class Internal;

// The solver contains some built in profiling (even for optimized code).
// The idea is that even without using external tools it is possible to get
// an overview of where time is spent.  This is enabled with the option
// 'profile', e.g., you might want to use 'cadical --profile=2 ...'.
//
// Profiling has a Heisenberg effect, since we rely on calling 'getrusage'
// instead of using profile counters and sampling.  For functions which are
// executed many times, this overhead is substantial (say 10%-20%).  For
// functions which are not executed many times there is in essence no
// overhead in measuring time spent in them.  These get a smaller profiling
// level, which is the second argument in the 'PROFILE' macro below.  Thus
// using '--profile=1' for instance should not add any penalty to the
// run-time, while '--profile=2' and higer levels slow down the solver.
//
// To profile say 'foo', just add another line 'PROFILE(foo)' and wrap
// the code to be profiled within a 'START (foo)' / 'STOP (foo)' block.

#define PROFILES \
PROFILE(analyze,3) \
PROFILE(bump,4) \
PROFILE(collect,2) \
PROFILE(connect,2) \
PROFILE(decide,3) \
PROFILE(elim,2) \
PROFILE(extend,4) \
PROFILE(minimize,4) \
PROFILE(parse,1) \
PROFILE(probe,2) \
PROFILE(propagate,4) \
PROFILE(reduce,2) \
PROFILE(restart,3) \
PROFILE(search,1) \
PROFILE(shrink,4) \
PROFILE(simplify,1) \
PROFILE(sublast,4) \
PROFILE(subsume,2) \

struct Profile {
  double value;
  const char * name;
  int level;
  Profile (const char * n, int l) : value (0), name (n), level (l) { }
};

struct Profiles {
  Internal * internal;
#define PROFILE(NAME, LEVEL) \
  Profile NAME;
  PROFILES
#undef PROFILE
  Profiles (Internal *);
};

};

#endif
