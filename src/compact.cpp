#include "internal.hpp"
#include "external.hpp"
#include "macros.hpp"

namespace CaDiCaL {

bool Internal::compactifying () {
  if (!opts.compact) return false;
  if (stats.conflicts < lim.compact) return false;
  int inactive = max_var - active_variables ();
  assert (inactive >= 0);
  if (!inactive) return false;
  return inactive >= opts.compactlim * max_var;
}

void Internal::compact () {
  START (compact);
  stats.compacts++;

  assert (!level);

  COVER (vals);
  COVER (phases);
  COVER (i2e);
  COVER (queue.first);
  COVER (vtab);
  COVER (ltab);
  COVER (ftab);
  COVER (btab);
  COVER (otab);
  COVER (ntab);
  COVER (ntab2);
  COVER (ptab);
  assert (!big);
  COVER (wtab);
  assert (!conflict);
  COVER (trail.size ());
  assert (clause.empty ());
  assert (levels.empty ());
  assert (analyzed.empty ());
  assert (minimized.empty ());
  COVER (probes.empty ());
  assert (control.size () == 1);
  COVER (clauses.size ());
  assert (resolved.empty ());
  COVER (esched.size ());

  inc.compact += opts.compactint;
  lim.compact = stats.conflicts + inc.compact;
  report ('c');
  STOP (compact);
}

};
