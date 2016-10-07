#ifndef _timer_hpp_INCLUDED
#define _timer_hpp_INCLUDED

namespace CaDiCaL {

struct Timer {
  double started;       // starting time (in seconds) for this phase
  Profile * profile;    // update this profile if phase stops
  Timer (double s, Profile * p) : started (s), profile (p) { }
  Timer () { }
  void update (double now) { profile->value += now - started; started = now; }
};

};

#endif
