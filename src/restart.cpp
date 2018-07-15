#include "internal.hpp"

namespace CaDiCaL {

// As observed by Chanseok Oh and implemented in MapleSAT solvers too,
// various mostly satisfiable instances benefit from long quiet phases
// without restart.  We implement this idea by prohibiting the Glucose style
// restart scheme in a geometric fashion, which is very similar to how
// originally restarts were scheduled in MiniSAT and earlier solver.  More
// precisely we start with say 1e3 = 1000 conflicts of Glucose restarts.
// Then in a "stabilizing" phase we disable restarts until 1e4 = 10000
// conflicts have passed. After that we switch back to regular Glucose style
// restarts until again 10 more conflicts than the previous limit.

bool Internal::stabilizing () {
  if (!opts.stabilize) return false;
  stats.stabchecks++;
  if (stats.conflicts >= lim.stabilize) {
    stabilization = !stabilization;
    if (stabilization) stats.stabphases++;
    VRB ("stabilizing", stats.stabphases,
      "reached stabilizing limit %ld after %ld conflicts",
      lim.stabilize, stats.conflicts);
    lim.stabilize *= opts.stabfactor;
    if (lim.stabilize <= stats.conflicts) lim.stabilize = stats.conflicts + 1;
    VRB ("stabilizing", stats.stabphases,
      "new stabilizing limit %ld conflicts", lim.stabilize);
    report (stabilization ? '[' : ']');
  }
  if (stabilization) stats.stabsuccess++;
  return stabilization;
}

// Restarts are scheduled by a variant of the Glucose scheme presented in
// our POS'15 paper using exponential moving averages.  There is a slow
// moving average of the average recent glucose level of learned clauses as
// well as a fast moving average of those glues.  If the end of base restart
// conflict interval has passed and the fast moving average is above a
// certain margin of the slow moving average then we restart.

bool Internal::restarting () {
  if (!opts.restart) return false;
  if (stabilizing ()) return false;
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
// exists to the top (in which case we do not reuse any level).

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
  lim.conflicts_at_last_restart = stats.conflicts;
  report ('r', 2);
  STOP (restart);
}

};

