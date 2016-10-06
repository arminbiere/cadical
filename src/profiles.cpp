#ifdef PROFILING

#include "cadical.hpp"

namespace CaDiCaL {

void Solver::start_profiling (double * p) {
  timers.push_back (Timer (seconds (), p));
}

void Solver::stop_profiling (double * p) {
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
  section ("run-time profiling data");
  const size_t size = sizeof profile / sizeof (double);
  struct { double value; const char * name; } profs[size];
  size_t i = 0;
#define PROFILE(NAME) \
  profs[i].value = profile.NAME; \
  profs[i].name = # NAME; \
  i++;
  PROFILES
#undef PROFILE
  assert (i == size);
  // Explicit bubble sort to avoid heap allocation since 'print_profile'
  // is also called during catching a signal after out of heap memory.
  // This only makes sense if 'profs' is allocated on the stack, and
  // not the heap, which should be the case.
  for (i = 0; i < size; i++) {
    for (size_t j = i + 1; j < size; j++)
      if (profs[j].value > profs[i].value)
        swap (profs[i].value, profs[j].value),
        swap (profs[i].name, profs[j].name);
    msg ("%12.2f %7.2f%% %s",
      profs[i].value, percent (profs[i].value, now), profs[i].name);
  }
  msg ("  ===============================");
  msg ("%12.2f %7.2f%% all", now, 100.0);
}

};

#endif
