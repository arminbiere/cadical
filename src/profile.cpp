#ifndef QUIET

#include "internal.hpp"

namespace CaDiCaL {

// Initialize all profile counters with constant name and profiling level.

Profiles::Profiles (Internal * s)
:
  internal (s)
#define PROFILE(NAME, LEVEL) \
  , NAME (#NAME, LEVEL)
  PROFILES
#undef PROFILE
{
}

void Internal::start_profiling (Profile * p, double s) {
  assert (p->level <= opts.profile);
  timers.push_back (Timer (s, p));
}

void Internal::stop_profiling (Profile * p, double s) {
  assert (p->level <= opts.profile);
  assert (!timers.empty ());
  Timer & t = timers.back ();
  assert (p == t.profile), (void) p;
  t.update (s);
  timers.pop_back ();
}

void Internal::update_all_timers (double now) {
  const vector<Timer>::iterator end = timers.end ();
  vector<Timer>::iterator i = timers.begin ();
  while (i != end) (*i++).update (now);
}

void Internal::print_profile (double now) {
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

#endif // ifndef QUIET
