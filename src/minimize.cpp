#include "internal.hpp"

#include "clause.hpp"
#include "iterator.hpp"
#include "macros.hpp"

#include <algorithm>

namespace CaDiCaL {

// Functions for learned clause minimization. We only have the recursive
// version, which actually is implemented recursively.  We also played with
// a non-recursive version, which however was more complex and slower.  The
// trick to keep potential stack exhausting recursion under guards is to
// explicitly limit the recursion depth.

// Instead of signatures as in the original implementation in MiniSAT and
// the corresponding paper, we use the 'poison' idea of Allen Van Gelder to
// mark unsuccessful removal attempts, then Donald Knuth's idea to abort
// minimization if only one literal was seen on the level and a new idea of
// also aborting if the earliest seen literal was assigned afterwards.

bool Internal::minimize_literal (int lit, int depth) {
  Flags & f = flags (lit);
  Var & v = var (lit);
  if (!v.level || f.removable () || f.clause ()) return true;
  if (v.decision () || f.poison () || v.level == level) return false;
  const Level & l = control[v.level];
  if (!depth && l.seen < 2) return false;
  if (v.trail <= l.trail) return false;
  if (depth > opts.minimizedepth) return false;
  bool res = true;
  if (v.reason) {
    const_literal_iterator end = v.reason->end (), i;
    int other;
    for (i = v.reason->begin (); res && i != end; i++)
      if ((other = *i) != lit)
	res = minimize_literal (-other, depth+1);
  } else res = minimize_literal (-v.other, depth+1);
  if (res) {
    f.set (REMOVABLE);
    if (!f.seen ()) {
      analyzed.push_back (lit);
      f.set (SEEN);
    }
  } else f.set (POISON);
  minimized.push_back (lit);
  if (!depth) LOG ("minimizing %d %s", lit, res ? "succeeded" : "failed");
  return res;
}

void Internal::minimize_clause () {
  START (minimize);
  LOG (clause, "minimizing first UIP clause");
  sort (clause.begin (), clause.end (), trail_smaller (this));
  assert (minimized.empty ());
  int_iterator j = clause.begin ();
  for (const_int_iterator i = j; i != clause.end (); i++)
    if (minimize_literal (-*i)) stats.minimized++;
    else flags (*j++ = *i).set (CLAUSE);
  LOG ("minimized %d literals", (long)(clause.end () - j));
  clause.resize (j - clause.begin ());
  clear_minimized ();
  check_clause ();
  STOP (minimize);
}

void Internal::clear_minimized () {
  for (const_int_iterator i = minimized.begin (); i != minimized.end (); i++)
    flags (*i).clear (POISON | REMOVABLE);
  for (const_int_iterator i = clause.begin (); i != clause.end (); i++)
    flags (*i).clear (CLAUSE);
  minimized.clear ();
}

};
