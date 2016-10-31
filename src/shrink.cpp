#include "internal.hpp"
#include "macros.hpp"

#include <algorithm>

namespace CaDiCaL {

// This is an extended minimization which goes over all alternative reasons
// as first explored in PrecoSAT and discussed by Allen Van Gelder later.
// The most important observation in PrecoSAT was that alternative reasons
// for resolution need to have all literals but one set to false and thus
// the true literal will be watched.  It subsumes clause minimization, but
// is more expensive and thus should be called only on clauses for which
// shrinking is useful (such as small clauses with small glue).  As in
// PrecoSAT we restrict traversal to follow the topological assignment order
// to avoid cycles (which yields unsound removals).

bool Internal::shrink_literal (int lit, int depth) {
  Flags & f = flags (lit);
  Var & v = var (lit);
  if (!v.level || f.removable () || f.clause ()) return true;
  if (v.decision () || f.poison () || v.level == level) return false;
  const Level & l = control[v.level];
  if (!depth && l.seen < 2) return false;
  if (v.trail <= l.trail) return false;
  if (depth > opts.shrinkdepth) return false;
  bool res = true;
  if (v.reason) {
    const_literal_iterator end = v.reason->end (), i;
    int other;
    for (i = v.reason->begin (); res && i != end; i++)
      if ((other = *i) != lit)
	res = shrink_literal (-other, depth+1);
  } else res = shrink_literal (-v.other, depth+1);
  if (res) {
    f.set (REMOVABLE);
    // if (!f.seen ()) analyzed.push_back (lit); // TODO?
  } else f.set (POISON);
  minimized.push_back (lit);
  if (!depth) LOG ("shrinking %d %s", lit, res ? "succeeded" : "failed");
  return res;
}


void Internal::shrink_clause () {
  START (shrink);
  LOG (clause, "shrinking minimized first UIP clause");
  sort (clause.begin (), clause.end (), trail_smaller (this));
  assert (minimized.empty ());
  int_iterator j = clause.begin ();
  for (const_int_iterator i = j; i != clause.end (); i++)
    if (shrink_literal (-*i)) stats.shrunken++, abort ();
    else flags (*j++ = *i).set (CLAUSE);
  LOG ("shrunken %d literals", (long)(clause.end () - j));
  clause.resize (j - clause.begin ());
  clear_minimized ();
  check_clause ();
  STOP (shrink);
}

};
