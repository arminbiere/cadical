#include "internal.hpp"

#include "macros.hpp"
#include "message.hpp"

namespace CaDiCaL {

bool Internal::restarting () {
  if (!opts.restart) return false;
  if (level < 2) return false;
  if (stats.conflicts <= lim.restart) return false;
  double s = slow_glue_avg, f = fast_glue_avg, l = opts.restartmargin * s;
  LOG ("EMA glue slow %.2f fast %.2f limit %.2f", s, f, l);
  return l <= f;
}

int Internal::reuse_trail () {
  if (!opts.reusetrail) return 0;
  long limit = bumped (next_decision_variable ());
  int res = 0;
  while (res < level && bumped (control[res + 1].decision) > limit)
    res++;
  if (res) stats.reused++;
  return res;
}

void Internal::restart () {
  START (restart);
  stats.restarts++;
  LOG ("restart %ld", stats.restarts);
  lim.lastlevel = level;
  backtrack (reuse_trail ());
  int delta = opts.restartint * stable * stable;
  if (delta < 1) delta = 1;
  if (delta > 200) delta = 200;
  lim.restart = stats.conflicts + delta;
  report ('r', 1);
  STOP (restart);
}

};

