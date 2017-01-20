#include "internal.hpp"

namespace CaDiCaL {

Limit::Limit () { memset (this, 0, sizeof *this); }

bool Internal::terminating () {
  if (lim.conflict >= 0 && stats.conflicts >= lim.conflict) return true;
  if (lim.decision >= 0 && stats.decisions >= lim.decision) return true;
  return false;
}

Inc::Inc () { memset (this, 0, sizeof *this); }

};
