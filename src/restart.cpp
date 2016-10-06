#include "solver.hpp"

namespace CaDiCaL {

bool Solver::blocking_enabled () {
  if (stats.conflicts > limits.blocking) {
    if (blocking.exploring) {
      inc.blocking += opts.restartblocklimit;
      limits.blocking = stats.conflicts + inc.blocking;
      blocking.exploring = false;
      VRB ("average blocking glue %.2f non-blocking %.2f ratio %.2f",
        (double) avg.glue.blocking, (double) avg.glue.nonblocking,
        relative (avg.glue.blocking, avg.glue.nonblocking));
      if (avg.glue.blocking >
          opts.restartblockmargin * avg.glue.nonblocking) {
        VRB ("exploiting non-blocking until %ld conflicts", limits.blocking);
        blocking.enabled = false;
      } else {
        VRB ("exploiting blocking until %ld conflicts", limits.blocking);
        blocking.enabled = true;
      }
    } else {
      blocking.exploring = true;
      limits.blocking =
        stats.conflicts + max (inc.blocking/10, (long)opts.restartblocklimit);
      if (blocking.enabled) {
        VRB ("exploring non-blocking until %ld conflicts", limits.blocking);
        blocking.enabled = false;
      } else {
        VRB ("exploring blocking until %ld conflicts", limits.blocking);
        blocking.enabled = true;
      }
    }
  }
  return blocking.enabled;
}

bool Solver::restarting () {
  if (!opts.restart) return false;
  if (stats.conflicts <= limits.restart.conflicts) return false;
  stats.restart.tried++;
  limits.restart.conflicts = stats.conflicts + opts.restartint;
  double s = avg.glue.slow, f = avg.glue.fast, l = opts.restartmargin * s;
  LOG ("EMA learned glue slow %.2f fast %.2f limit %.2f", s, f, l);
  if (l > f) {
    if (opts.restartemaf1) {
      if (avg.frequency.unit >= opts.emaf1lim) {
        stats.restart.unit++;
        LOG ("high unit frequency restart", (double) avg.frequency.unit);
        return true;
      } else LOG ("low unit frequency", (double) avg.frequency.unit);
    }
    stats.restart.unforced++;
    LOG ("unforced restart");
    return false;
  } else {
    LOG ("forced restart");
    stats.restart.forced++;
  }
  return true;
}

int Solver::reuse_trail () {
  if (!opts.reusetrail) return 0;
  long limit = var (next_decision_variable ()).bumped;
  int res = 0;
  while (res < level && var (levels[res + 1].decision).bumped > limit)
    res++;
  if (res) { stats.restart.reused++; LOG ("reusing trail %d", res); }
  return res;
}

void Solver::restart () {
  START (restart);
  stats.restart.count++;
  LOG ("restart %ld", stats.restart.count);
  backtrack (reuse_trail ());
  report ('r', 1);
  STOP (restart);
}

};

