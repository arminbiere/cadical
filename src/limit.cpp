#include "internal.hpp"

#include <cstring>

namespace CaDiCaL {

Limit::Limit () {

  memset (this, 0, sizeof *this);

  // Otherwise we have a redundant 'forced rescheduling' the first time.
  //
  vivify_wait_reschedule = 1;
  probe_wait_reschedule = 1;
}

bool Internal::terminating () {
  if (lim.conflict >= 0 && stats.conflicts >= lim.conflict) return true;
  if (lim.decision >= 0 && stats.decisions >= lim.decision) return true;
  return false;
}

Inc::Inc () { memset (this, 0, sizeof *this); }

};
