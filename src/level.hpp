#ifndef _level_hpp_INCLUDED
#define _level_hpp_INCLUDED

#include <climits>

namespace CaDiCaL {

// For each new decision we increase the decision level and push a 'Level'
// on the 'control' stack.  The information gather here is used in
// 'reuse_trail' and for early aborts in clause minimization.

struct Level {
  int decision;         // decision literal of level
  int seen;             // how many variables seen during 'analyze'
  int trail;            // smallest trail position seen

  void reset () { seen = 0, trail = INT_MAX; }

  Level (int d) : decision (d) { reset (); }
  Level () { }
};

};

#endif
