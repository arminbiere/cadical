#include "internal.hpp"

namespace CaDiCaL {

bool Internal::rephasing () {
  if (!opts.rephase) return false;
  return stats.conflicts > lim.rephase;
}

void Internal::rephase () {
  stats.rephased++;
  LOG ("rephase %ld", stats.rephased);
  signed char val = opts.phase ? 1 : -1;
  if (stats.rephased & 1) val = -val;
  for (int idx = 1; idx <= max_var; idx++) phases[idx] = val;
  backtrack ();
  inc.rephase *= 2;
  lim.rephase = stats.conflicts + inc.rephase;
  LOG ("next rephase after %ld conflicts", lim.rephase);
  report ('~');
}

};
