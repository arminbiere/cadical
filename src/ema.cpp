#include "internal.hpp"

namespace CaDiCaL {

// Updating an exponential moving average is placed here since we want to
// log both updates and phases of initialization, thus need 'LOG'.

void EMA::update (Internal * internal, double y, const char * name) {
#ifndef LOGGING
  (void) internal, (void) name;
#endif
  // This is the common exponential moving average update.

  value += beta * (y - value);
  LOG ("update %s EMA with %g beta %g yields %g", name, y, beta, value);

  // However, we used the upper approximation 'beta' of 'alpha'.  The idea
  // is that 'beta' slowly moves down to 'alpha' to smoothly initialize
  // the exponential moving average.  This technique was used in 'Splatz'.

  // We maintain 'beta = 2^-period' until 'beta < alpha' and then set it to
  // 'alpha'.  The period gives the number of updates this 'beta' is used.
  // So for smaller and smaller 'beta' we wait exponentially longer until
  // 'beta' is halfed again.  The sequence of 'beta's is
  //
  //   1,
  //   1/2, 1/2,
  //   1/4, 1/4, 1/4, 1/4
  //   1/8, 1/8, 1/8, 1/8, 1/8, 1/8, 1/8, 1/8,
  //   ...
  //
  //  We did not derive this formally, but observed it during logging.  This
  //  is in 'Splatz' but not published yet, e.g., was not in POS'15.

  if (beta <= alpha || wait--) return;
  wait = period = 2*(period + 1) - 1;
  beta *= 0.5;
  if (beta < alpha) beta = alpha;
  LOG ("new %s EMA wait = period = %" PRId64 ", beta = %g", name, wait, beta);
}

}
