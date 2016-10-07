#include "solver.hpp"

namespace CaDiCaL {

Profiles::Profiles (Solver * s)
:
  solver (s)
#define PROFILE(NAME, LEVEL) \
  , NAME (#NAME, LEVEL)
  PROFILES
#undef PROFILE
{
}

void Solver::start_profiling (Profile * p) {
  timers.push_back (Timer (seconds (), p));
}

void Solver::stop_profiling (Profile * p) {
  assert (!timers.empty ());
  Timer & t = timers.back ();
  assert (p == t.profile), (void) p;
  t.update (seconds ());
  timers.pop_back ();
}

void Solver::update_all_timers (double now) {
  for (size_t i = 0; i < timers.size (); i++)
    timers[i].update (now);
}

void Solver::print_profile (double now) {
  update_all_timers (now);
  SECTION ("run-time profiling data");
  const size_t size = sizeof profiles / sizeof (Profile);
  struct Profile * profs[size];
  size_t n = 0;
#define PROFILE(NAME,LEVEL) \
  if (LEVEL <= opts.profile) \
    profs[n++] = &profiles.NAME;
  PROFILES
#undef PROFILE
  assert (n <= size);
  // Explicit bubble sort to avoid heap allocation since 'print_profile'
  // is also called during catching a signal after out of heap memory.
  // This only makes sense if 'profs' is allocated on the stack, and
  // not the heap, which should be the case.
  for (size_t i = 0; i < n; i++) {
    for (size_t j = i + 1; j < n; j++)
      if (profs[j]->value > profs[i]->value)
        swap (profs[i], profs[j]);
    MSG ("%12.2f %7.2f%% %s",
      profs[i]->value, percent (profs[i]->value, now), profs[i]->name);
  }
  MSG ("  ===============================");
  MSG ("%12.2f %7.2f%% all", now, 100.0);
}

};
