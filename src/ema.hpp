#ifndef _ema_hpp_INCLUDED
#define _ema_hpp_INCLUDED

namespace CaDiCaL {

struct Internal;

// This is a more complex generic exponential moving average class to
// support  more robust initialization (see comments in the 'update'
// implementation).

struct EMA {
  double value;         // current average value
  double alpha;         // percentage contribution of new values
  double beta;          // current upper approximation of alpha
  int64_t wait;         // count-down using 'beta' instead of 'alpha'
  int64_t period;       // length of current waiting phase

  EMA () : value (0), alpha (0), beta (0), wait (0), period (0) { }

  EMA (double a) :
     value (0), alpha (a), beta (1.0), wait (0), period (0)
  {
    assert (0 <= alpha), assert (alpha <= beta), assert (beta <= 1);
  }

  operator double () const { return value; }
  void update (Internal *, double y, const char * name);
};

}

/*------------------------------------------------------------------------*/

// Compact average update and initialization macros for better logging.

#define UPDATE_AVERAGE(A,Y) \
do { A.update (internal, (Y), #A); } while (0)

#define INIT_EMA(E,WINDOW) \
do { \
  assert ((WINDOW) >= 1); \
  double ALPHA = 1.0 / (double)(WINDOW); \
  E = EMA (ALPHA); \
  LOG ("init " #E " EMA target alpha %g window %d", ALPHA, (int)WINDOW); \
} while (0)

/*------------------------------------------------------------------------*/

#endif
