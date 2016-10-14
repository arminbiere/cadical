#include "internal.hpp"

#include "macros.hpp"
#include "message.hpp"

namespace CaDiCaL {

bool Internal::restarting () {
  if (!opts.restart) return false;
  if (stats.conflicts <= restart_limit) return false;
  restart_limit = stats.conflicts + opts.restartint;
  double s = slow_glue_avg, f = fast_glue_avg, l = opts.restartmargin * s;
  LOG ("EMA learned glue slow %.2f fast %.2f limit %.2f", s, f, l);
  return l <= f;
}

int Internal::reuse_trail () {
  if (!opts.reusetrail) return 0;
  long limit = var (next_decision_variable ()).bumped;
  int res = 0;
  while (res < level && var (control[res + 1].decision).bumped > limit)
    res++;
  if (res) stats.reused++;
  return res;
}

void Internal::restart () {
  START (restart);
  stats.restarts++;
  LOG ("restart %ld", stats.restarts);
  backtrack (reuse_trail ());
  report ('r', 1);
  STOP (restart);
}

};

