#include "internal.hpp"

namespace CaDiCaL {

bool Internal::rephasing () {
  if (!opts.rephase) return false;
  return stats.conflicts > lim.rephase;
}

void Internal::rephase () {
  stats.rephased++;
  VRB ("rephase", stats.rephased,
    "reached rephase limit %ld after %ld conflicts",
    lim.rephase, stats.conflicts);
  backtrack ();
  signed char val = opts.phase ? 1 : -1;
  char type;
  switch (stats.rephased % 4) {
    case 0:
    default:
      type = 'O';
      LOG ("switching to original phase %d", val);
      for (int idx = 1; idx <= max_var; idx++) phases[idx] = val;
      break;
    case 1:
      type = 'F';
      LOG ("flipping all phases individually");
      for (int idx = 1; idx <= max_var; idx++) phases[idx] *= -1;
      break;
    case 2:
      type = 'I';
      LOG ("switching to inverted phase %d", -val);
      for (int idx = 1; idx <= max_var; idx++) phases[idx] = -val;
      break;
    case 3:
      type = 'R';
      LOG ("resetting all phases randomly");
      for (int idx = 1; idx <= max_var; idx++) {
        unsigned tmp = stats.rephased * 123123311u;
        tmp += opts.seed;
        tmp *= 558064459u;
        tmp += idx;
        tmp *= 43243507u;
        tmp ^= (tmp >> 16);
        tmp ^= (tmp >> 8);
        tmp ^= (tmp >> 4);
        tmp ^= (tmp >> 2);
        tmp ^= (tmp >> 1);
        phases[idx] = (tmp & 1) ? -1 : 1;
      }
      break;
  }
  inc.rephase += opts.rephaseinc;
  VRB ("rephase", stats.rephased, "new rephase increment %ld", inc.rephase);
  lim.rephase += inc.rephase;
  if (lim.rephase <= stats.conflicts) lim.rephase = stats.conflicts + 1;
  VRB ("rephase", stats.rephased, "new rephase limit %ld", lim.rephase);
  report (type, 1);
}

};
