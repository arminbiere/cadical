#include "internal.hpp"

namespace CaDiCaL {

// Restarts are scheduled by a variant of the Glucose scheme presented in
// our POS'15 paper using exponential moving averages.  There is a slow
// moving average of the average recent glue level of learned clauses as
// well as fast moving average of those glues.  If the end of base restart
// conflict interval has passed and the fast moving average is above a
// certain margin of the slow moving average then we restart.

bool Internal::restarting () {
  if (!opts.restart) return false;
  if (stats.conflicts <= lim.restart) return false;
  if (level < 2) return false;
  if (level < fast_glue_avg) return false;
  double s = slow_glue_avg, f = fast_glue_avg, l = opts.restartmargin * s;
  LOG ("EMA glue slow %.2f fast %.2f limit %.2f", s, f, l);
  return l <= f;
}

// This is Marijn's reuse trail idea.  Instead of always backtracking to the
// top we figure out which decisions would be made again anyhow and only
// backtrack to the level of the last such decision or if no such decision
// exists to the top (in which case we do reuse any level).

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
  backtrack (reuse_trail ());
  lim.restart = stats.conflicts + opts.restartint;
  report ('R', 2);
  STOP (restart);
}

};

