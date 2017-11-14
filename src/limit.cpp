#include "internal.hpp"

namespace CaDiCaL {

Limit::Limit () { memset (this, 0, sizeof *this); }

bool Internal::terminating () {
  if (termination) {
    LOG ("termination forced");
    return true;
  }
  if (lim.conflict >= 0 && stats.conflicts >= lim.conflict) {
    LOG ("conflict limit %ld reached", lim.conflict);
    return true;
  }
  if (lim.decision >= 0 && stats.decisions >= lim.decision) {
    LOG ("decision limit %ld reached", lim.decision);
    return true;
  }
  return false;
}

Inc::Inc () { memset (this, 0, sizeof *this); }

};
