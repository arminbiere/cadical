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

  // We produce a compactifying garbage collector like map of old 'src' to
  // new 'dst' variables.  Inactive variables are just skipped except for
  // fixed ones which will be mapped to the first fixed variable (in the
  // appropriate phase).  This avoids to handle the case 'fixed value'
  // seperately as it is done in Lingeling, where fixed variables are
  // mapped to the internal variable '1'.
  //
  int * map, dst = 1, first_fixed = 0, first_fixed_val = 0;
  NEW (map, int, max_var + 1);
  map[0] = 0;
  for (int src = 1; src <= max_var; src++) {
    const Flags & f = flags (src);
    if (f.active ()) map[src] = dst++;
    else if (!f.fixed ()) map[src] = 0;
    else {
      const int tmp = val (src);
      if (!first_fixed) first_fixed_val = tmp, first_fixed = dst;
      map[src] = (tmp == first_fixed_val) ? first_fixed : -first_fixed;
      dst++;
    }
  }

  int new_max_var = dst;
  size_t new_vsize = dst + 1;

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

  COVER (external->e2i);

  DEL (map, int, max_var);

  max_var = new_max_var;
  vsize = new_vsize;

  inc.compact += opts.compactint;
  lim.compact = stats.conflicts + inc.compact;
  report ('c');
  STOP (compact);
}

};
