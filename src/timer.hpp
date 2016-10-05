#ifndef _timer_hpp_INCLUDED
#define _timer_hpp_INCLUDED

#ifdef PROFILING

namespace CaDiCaL {

struct Timer {
  double started;       // starting time (in seconds) for this phase
  double * profile;     // update this profile if phase stops
  Timer (double s, double * p) : started (s), profile (p) { }
  Timer () { }
  void update (double now) { *profile += now - started; started = now; }
};

};

#endif

#endif
