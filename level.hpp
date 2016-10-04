#ifndef _level_hpp_INCLUDED
#define _level_hpp_INCLUDED

namespace CaDiCaL {

struct Level {
  int decision;         // decision literal of level
  int seen;             // how man variables seen during 'analyze'
  int trail;            // smallest trail position seen
  void reset () { seen = 0, trail = INT_MAX; }
  Level (int d) : decision (d) { reset (); }
  Level () { }
};

};

#endif
