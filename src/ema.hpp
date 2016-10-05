#ifndef _ema_hpp_INCLUDED
#define _ema_hpp_INCLUDED

#include <cassert>

namespace CaDiCaL {

class Solver;

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
  void update (Solver &, double y, const char * name);
};

};

#endif
