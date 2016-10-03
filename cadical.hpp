#ifndef _cadical_hpp_INCLUDED
#define _cadical_hpp_INCLUDED

#include <vector>

#include <climits>
#include <cassert>

#include "options.hpp"
#include "clause.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

using namespace std;

/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/

struct Var {

  int level;            // decision level
  int trail;            // trail level

  bool seen;            // analyzed in 'analyze' and will be bumped
  bool poison;          // can not be removed during clause minimization
  bool removable;       // can be removed during clause minimization

  int prev, next;       // double links for decision VMTF queue
  long bumped;          // enqueue time stamp for VMTF queue

  Clause * reason;      // implication graph edge

  Var () :
    seen (false), poison (false), removable (false),
    prev (0), next (0), bumped (0)
  { }
};

/*------------------------------------------------------------------------*/

struct Watch {
  int blit;             // if blocking literal is true do not visit clause
  Clause * clause;
  Watch (int b, Clause * c) : blit (b), clause (c) { }
  Watch () { }
};

/*------------------------------------------------------------------------*/

typedef vector<Watch> Watches;          // of one literal

/*------------------------------------------------------------------------*/

struct Level {
  int decision;         // decision literal of level
  int seen;             // how man variables seen during 'analyze'
  int trail;            // smallest trail position seen
  void reset () { seen = 0, trail = INT_MAX; }
  Level (int d) : decision (d) { reset (); }
  Level () { }
};

/*------------------------------------------------------------------------*/

// We have a more complex generic exponential moving average struct here
// for more robust initialization (see comments before 'update' below).

struct EMA {
  double value;         // current average value
  double alpha;         // percentage contribution of new values
  double beta;          // current upper approximation of alpha
  long wait;            // count-down using 'beta' instead of 'alpha'
  long period;          // length of current waiting phase

  EMA (double a = 0, double b = 0) :
     value (0), alpha (a), beta (b), wait (0), period (0)
  {
    assert (0 <= alpha), assert (alpha <= beta), assert (beta <= 1);
  }
  operator double () const { return value; }
  void update (double y, const char * name);
};

/*------------------------------------------------------------------------*/

struct AVG {
  double value;
  long count;
  AVG () : value (0), count (0) { }
  operator double () const { return value; }
  void update (double y, const char * name);
};

/*------------------------------------------------------------------------*/

#ifdef PROFILING        // enabled by './configure -p'

struct Timer {
  double started;       // starting time (in seconds) for this phase
  double * profile;     // update this profile if phase stops
  Timer (double s, double * p) : started (s), profile (p) { }
  Timer () { }
  void update (double now) { *profile += now - started; started = now; }
};

#endif

/*------------------------------------------------------------------------*/

class Solver {
  Options opts;
};

};

#endif
