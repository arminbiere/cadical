#include "internal.hpp"

#include "clause.hpp"
#include "iterator.hpp"
#include "macros.hpp"

#include <algorithm>

namespace CaDiCaL {

// Functions for learned clause minimization. We only have the recursive
// version, which actually is implemented recursively.  We also played with
// a non-recursive version, which however was more complex and slower.  The
// trick to keep pontential stack exhausting recursion under guards is to
// explicitly limit the recursion depth.

// Instead of signatures as in the original implementation in MiniSAT and
// the corresponding paper, we use Allen Van Gelders 'poison' idea to mark
// unsuccesful removal attempts, Donald Knuth's idea to abort minimization
// if only one literal was seen on the level and a new idea of also aborting
// if the earliest seen literal was assigned afterwards.

bool Internal::minimize_literal (int lit, int depth) {
  Var & v = var (lit);
  Tag & t = tag (lit);
  if (!v.level || t.removable () || (depth && t.seen ())) return true;
  if (!v.reason || t.poison () || v.level == level) return false;
  const Level & l = control[v.level];
  if (!depth && l.seen < 2) return false;
  if (v.trail <= l.trail) return false;
  if (depth > opts.minimizedepth) return false;
  const_literal_iterator end = v.reason->end ();
  bool res = true;
  for (const_literal_iterator i = v.reason->begin (); res && i != end; i++) {
    int other = *i;
    if (other == lit) continue;
    res = minimize_literal (-other, depth+1);
  }
  if (res) t.mark (Tag::REMOVABLE); else t.mark (Tag::POISON);
  minimized.push_back (lit);
  if (!depth) LOG ("minimizing %d %s", lit, res ? "succeeded" : "failed");
  return res;
}

// We try to minimize the first UIP clause by trying to remove away literals
// on smaller decision level first.  This makes more room for depth bounded
// minimization even though we have not really seen cases where the depth
// limit is hit and results in substantially less succesful minimization.

struct trail_smaller {
  Internal * internal;
  trail_smaller (Internal * s) : internal (s) { }
  bool operator () (int a, int b) {
    return internal->var (a).trail < internal->var (b).trail;
  }
};

void Internal::minimize_clause () {
  if (!opts.minimize) return;
  START (minimize);
  LOG (clause, "minimizing first UIP clause");
  stable_sort (clause.begin (), clause.end (), trail_smaller (this));
  assert (minimized.empty ());
  stats.learned += clause.size ();
  int_iterator j = clause.begin ();
  for (const_int_iterator i = clause.begin (); i != clause.end (); i++)
    if (minimize_literal (-*i)) stats.minimized++;
    else *j++ = *i;
  LOG ("minimized %d literals", (long)(clause.end () - j));
  clause.resize (j - clause.begin ());
  for (const_int_iterator i = minimized.begin (); i != minimized.end (); i++)
    tag (*i).reset ();
  minimized.clear ();
  STOP (minimize);
  check_clause ();
}

};
