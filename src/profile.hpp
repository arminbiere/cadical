#ifndef QUIET
#ifndef _profiles_h_INCLUDED
#define _profiles_h_INCLUDED

namespace CaDiCaL {

class Internal;

/*------------------------------------------------------------------------*/

// The solver contains some built in profiling (even for optimized code).
// The idea is that even without using external tools it is possible to get
// an overview of where time is spent.  This is enabled with the option
// 'profile', e.g., you might want to use '--profile=3', or even higher
// values for more detailed profiling information.  Currently the default is
// '--profile=2', which should only induce a tiny profiling overhead.
//
// Profiling has a Heisenberg effect, since we rely on calling 'getrusage'
// instead of using profile counters and sampling.  For functions which are
// executed many times, this overhead is substantial (say 10%-20%).  For
// functions which are not executed many times there is in essence no
// overhead in measuring time spent in them.  These get a smaller profiling
// level, which is the second argument in the 'PROFILE' macro below.  Thus
// using '--profile=1' for instance should not add any penalty to the
// run-time, while '--profile=3' and higer levels slow down the solver.
//
// To profile say 'foo', just add another line 'PROFILE(foo)' and wrap
// the code to be profiled within a 'START (foo)' / 'STOP (foo)' block.

/*------------------------------------------------------------------------*/

// Profile counters for functions which are not compiled in should be
// removed. This is achieved by adding a wrapper macro for them here.

/*------------------------------------------------------------------------*/

#define PROFILES \
PROFILE(analyze,3) \
PROFILE(bump,4) \
PROFILE(collect,2) \
PROFILE(compact,2) \
PROFILE(connect,2) \
PROFILE(decide,3) \
PROFILE(decompose,2) \
PROFILE(elim,2) \
PROFILE(extend,4) \
PROFILE(minimize,4) \
PROFILE(parse,1) \
PROFILE(probe,2) \
PROFILE(deduplicate,2) \
PROFILE(propagate,4) \
PROFILE(reduce,2) \
PROFILE(restart,3) \
PROFILE(search,1) \
PROFILE(simplify,1) \
PROFILE(subsume,2) \
PROFILE(transred,2) \
PROFILE(vivify,2) \

/*------------------------------------------------------------------------*/

// See 'START' and 'STOP' in 'macros.hpp' too.

struct Profile {

  double value;      // accumulated time
  const char * name; // name of the profiled function (or 'phase')
  const int level;   // allows to cheaply test if profiling is enabled

  Profile (const char * n, int l) : value (0), name (n), level (l) { }
};

/*------------------------------------------------------------------------*/

// There is a timer stack for profiling functions.

struct Timer {

  double started;       // starting time (in seconds) for this phase
  Profile * profile;    // update this profile if phase stops

  Timer (double s, Profile * p) : started (s), profile (p) { }
  Timer () { }

  void update (double now) { profile->value += now - started; started = now; }
};

/*------------------------------------------------------------------------*/

struct Profiles {
  Internal * internal;
#define PROFILE(NAME, LEVEL) \
  Profile NAME;
  PROFILES
#undef PROFILE
  Profiles (Internal *);
};

};

/*------------------------------------------------------------------------*/

// Macros for Profiling support.

#ifndef QUIET //...........................................................

#define START(P,ARGS...) \
do { \
  if (internal->profiles.P.level > internal->opts.profile) break; \
  internal->start_profiling (&internal->profiles.P, ##ARGS); \
} while (0)

#define STOP(P,ARGS...) \
do { \
  if (internal->profiles.P.level > internal->opts.profile) break; \
  internal->stop_profiling (&internal->profiles.P, ##ARGS); \
} while (0)

#define SWITCH_AND_START(F,T,P) \
do { \
  const double N = process_time (); \
  const int L = internal->opts.profile; \
  if (internal->profiles.F.level <= L)  STOP (F, N); \
  if (internal->profiles.T.level <= L) START (T, N); \
  if (internal->profiles.P.level <= L) START (P, N); \
} while (0)

#define STOP_AND_SWITCH(P,F,T) \
do { \
  const double N = process_time (); \
  const int L = internal->opts.profile; \
  if (internal->profiles.P.level <= L)  STOP (P, N); \
  if (internal->profiles.F.level <= L)  STOP (F, N); \
  if (internal->profiles.T.level <= L) START (T, N); \
} while (0)

#else // ifndef QUIET //...................................................

#define START(ARGS...) do { } while (0)
#define STOP(ARGS...) do { } while (0)

#define SWITCH_AND_START(ARGS...) do { } while (0)
#define STOP_AND_SWITCH(ARGS...) do { } while (0)

#endif
/*------------------------------------------------------------------------*/

#endif // ifndef _profiles_h_INCLUDED
#endif // ifndef QUIET
