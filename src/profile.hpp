#ifndef _profiles_h_INCLUDED
#define _profiles_h_INCLUDED

/*------------------------------------------------------------------------*/
#ifndef QUIET
/*------------------------------------------------------------------------*/
#include <cstdint>
#include <tuple>

namespace CaDiCaL {

struct Internal;

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
// run-time, while '--profile=3' and higher levels slow down the solver.
//
// To profile say 'foo', just add another line 'PROFILE(foo, LEVEL)' and a
// profile context to the code to be profiled via 'PROFILE_SCOPE (foo)'.

/*------------------------------------------------------------------------*/

// Profile counters for functions which are not compiled in should be
// removed. This is achieved by adding a wrapper macro for them here.

/*------------------------------------------------------------------------*/

#ifdef PROFILE_MODE
#define MROFILE PROFILE
#else
#define MROFILE(...) /**/
#endif

#define PROFILES \
  PROFILE (analyze, 3) \
  MROFILE (analyzestable, 4) \
  MROFILE (analyzeunstable, 4) \
  PROFILE (backbone, 2) \
  PROFILE (backward, 3) \
  PROFILE (block, 2) \
  PROFILE (bump, 4) \
  PROFILE (checking, 2) \
  PROFILE (cdcl, 1) \
  PROFILE (collect, 3) \
  PROFILE (compact, 3) \
  PROFILE (condition, 2) \
  PROFILE (congruence, 2) \
  PROFILE (congruencemerge, 4) \
  PROFILE (congruencematching, 4) \
  PROFILE (connect, 3) \
  PROFILE (copy, 4) \
  PROFILE (cover, 2) \
  PROFILE (decide, 3) \
  PROFILE (decompose, 3) \
  PROFILE (definition, 2) \
  PROFILE (elim, 2) \
  PROFILE (factor, 2) \
  PROFILE (fastelim, 2) \
  PROFILE (extend, 3) \
  PROFILE (extract, 3) \
  PROFILE (extractands, 4) \
  PROFILE (extractbinaries, 4) \
  PROFILE (extractites, 4) \
  PROFILE (extractxors, 4) \
  PROFILE (instantiate, 2) \
  PROFILE (lucky, 2) \
  PROFILE (lookahead, 2) \
  PROFILE (minimize, 4) \
  PROFILE (shrink, 4) \
  PROFILE (parse, 0) /* As 'opts.profile' might change in parsing*/ \
  PROFILE (probe, 2) \
  PROFILE (deduplicate, 3) \
  PROFILE (propagate, 4) \
  MROFILE (propstable, 4) \
  MROFILE (propunstable, 4) \
  PROFILE (reduce, 3) \
  PROFILE (restart, 3) \
  PROFILE (restore, 2) \
  PROFILE (search, 1) \
  PROFILE (solve, 0) \
  PROFILE (stable, 2) \
  PROFILE (sweep, 2) \
  PROFILE (sweepbackbone, 3) \
  PROFILE (sweepequivalences, 3) \
  PROFILE (sweepflip, 4) \
  PROFILE (sweepimplicant, 4) \
  PROFILE (sweepsolve, 4) \
  PROFILE (preprocess, 2) \
  PROFILE (simplify, 1) \
  PROFILE (subsume, 2) \
  PROFILE (ternary, 2) \
  PROFILE (transred, 3) \
  PROFILE (unstable, 2) \
  PROFILE (vivify, 2) \
  PROFILE (walk, 2) \
  PROFILE (walkpick, 3) \
  PROFILE (walkbreak, 4) \
  PROFILE (walkflip, 3) \
  PROFILE (walkflipbroken, 4) \
  PROFILE (walkflipWL, 3) \
  PROFILE (walktransferweights, 3) \
  PROFILE (walkwrv, 3) \
  PROFILE (warmup, 3)

/*------------------------------------------------------------------------*/

struct Profile {

  bool active;
  double value;          // accumulated time
  int64_t search_ticks;  // accumulated ticks
  double started;        // started time if active
  int64_t started_ticks; // accumulated ticks
  const char *name;      // name of the profiled function (or 'phase')
  const int level;       // allows to cheaply test if profiling is enabled

  Profile (const char *n, int l)
      : active (false), value (0), search_ticks (0), name (n), level (l) {}
};

struct Profiles {
  Internal *internal;
#define PROFILE(NAME, LEVEL) Profile NAME;
  PROFILES
#undef PROFILE
  Profiles (Internal *);
};

} // namespace CaDiCaL

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

// C++ 11 version of std::index_sequence<N>
template <std::size_t... Is> struct ProfileIndices {};

template <typename... Profiles> struct ProfileContext {
  Internal *internal;
  std::tuple<Profiles...> profiles;

  ProfileContext (Internal *internal, Profiles... profiles);
  ~ProfileContext ();

  void enterContext ();
  void leaveContext ();

private:
  template <size_t... Is> void enterContext (ProfileIndices<Is...> indices);
  template <size_t... Is> void leaveContext (ProfileIndices<Is...> indices);
};

struct ResumeProfile {
  Profile &profile;
  bool condition;
  bool entered;

  ResumeProfile (Profile &profile, bool condition = true)
      : profile (profile), condition (condition), entered (false) {}

  void enterContext (Internal *internal, double time, int64_t ticks,
                     int level);
  void leaveContext (Internal *internal, double time, int64_t ticks,
                     int level);
};

struct PauseProfile {
  Profile &profile;
  bool condition;
  bool entered;

  PauseProfile (Profile &profile, bool condition = true)
      : profile (profile), condition (condition), entered (false) {}

  void enterContext (Internal *internal, double time, int64_t ticks,
                     int level);
  void leaveContext (Internal *internal, double time, int64_t ticks,
                     int level);
};

} // namespace CaDiCaL

// Macros for profiling support.
#define PROFILE_SCOPE(P) \
  ProfileContext<ResumeProfile> P##Profile{ \
      internal, \
      ResumeProfile{internal->profiles.P}, \
  };

#define PROFILE_SCOPE2(P, P2) \
  ProfileContext<ResumeProfile, ResumeProfile> P##Profile{ \
      internal, \
      ResumeProfile{internal->profiles.P}, \
      ResumeProfile{internal->profiles.P2}, \
  };

#define PROFILE_SCOPE_EARLY_EXIT(P) P##Profile.leaveContext ();

#define PROFILE_SCOPE_INTERRUPT_WITH(P, NEW) \
  ProfileContext<ResumeProfile, PauseProfile> P##ExchangeProfile{ \
      internal, \
      ResumeProfile{internal->profiles.NEW}, \
      PauseProfile{internal->profiles.P}, \
  };

#define PROFILE_SCOPE_WALK(P) \
  ProfileContext<ResumeProfile, PauseProfile, PauseProfile> P##Profile{ \
      internal, \
      ResumeProfile{internal->profiles.P}, \
      PauseProfile{internal->profiles.stable}, \
      PauseProfile{internal->profiles.unstable}, \
  };

#define PROFILE_SCOPE_SEARCH(P, stable) \
  ProfileContext<ResumeProfile, ResumeProfile, ResumeProfile> P##Profile{ \
      internal, \
      ResumeProfile{internal->profiles.P}, \
      ResumeProfile{internal->profiles.stable, stable}, \
      ResumeProfile{internal->profiles.unstable, !stable}, \
  };

#define PROFILE_SCOPE_SEARCH_STABILIZE() \
  ProfileContext<PauseProfile, PauseProfile> P##Profile{ \
      internal, \
      PauseProfile{internal->profiles.stable}, \
      PauseProfile{internal->profiles.unstable}, \
  };

#define PROFILE_SCOPE_SIMPLIFY(P) \
  ProfileContext<ResumeProfile, ResumeProfile, PauseProfile, PauseProfile, \
                 PauseProfile> \
      P##Profile{ \
          internal, \
          ResumeProfile{internal->profiles.simplify}, \
          ResumeProfile{internal->profiles.P}, \
          PauseProfile{internal->profiles.stable}, \
          PauseProfile{internal->profiles.unstable}, \
          PauseProfile{internal->profiles.search}, \
      };

#else // !QUIET

#define PROFILE_SCOPE(P)
#define PROFILE_SCOPE2(P, P2)
#define PROFILE_SCOPE_EARLY_EXIT(P)
#define PROFILE_SCOPE_INTERRUPT_WITH(P, NEW)

#define PROFILE_SCOPE_WALK(P)
#define PROFILE_SCOPE_SEARCH(P, stable)
#define PROFILE_SCOPE_SEARCH_STABILIZE()
#define PROFILE_SCOPE_SIMPLIFY(P)

#endif // QUIET

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

struct ModeResumeContext {
  Internal *internal;
  int mode;
  bool entered;

  ModeResumeContext (Internal *internal, int mode);
  ~ModeResumeContext ();

  void enterContext ();
  void leaveContext ();
};

struct ModePauseContext {
  Internal *internal;
  int mode;
  bool entered;

  ModePauseContext (Internal *internal, int mode);
  ~ModePauseContext ();

  void enterContext ();
  void leaveContext ();
};

} // namespace CaDiCaL

// Macros for mode support.
#define MODE_REQUIRE(M) internal->require_mode (Internal::Mode::M);

#define MODE_SCOPE(M) \
  ModeResumeContext M##Mode{internal, Internal::Mode::M};

#define MODE_SCOPE_PAUSE(M) \
  ModePauseContext M##Mode{internal, Internal::Mode::M};

#define MODE_SCOPE_EARLY_EXIT(P) P##Mode.leaveContext ();

#define MODE_SCOPE_WALK(M) \
  MODE_REQUIRE (SEARCH); \
  MODE_SCOPE (M); \
  assert (!internal->preprocessing);

#define MODE_SCOPE_SIMPLIFY(M) \
  MODE_SCOPE_PAUSE (SEARCH); \
  MODE_SCOPE (M); \
  MODE_SCOPE (SIMPLIFY);

#endif // ifndef _profiles_h_INCLUDED
