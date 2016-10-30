#ifndef _level_hpp_INCLUDED
#define _level_hpp_INCLUDED

#include <climits>

namespace CaDiCaL {

// For each new decision we increase the decision level
// and push a 'Level' on the 'control' stack.  This is used in
// 'reuse_trail' and for early aborts in clause minimization.

struct Level {
  int decision;         // decision literal of level
  int seen;             // how many variables seen during 'analyze'
  void reset () { seen = 0; }
  Level (int d) : decision (d), seen (0) { }
  Level () { }
};

};

#endif
