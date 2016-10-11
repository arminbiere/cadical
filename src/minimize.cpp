#include "internal.hpp"

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
  if (!v.level || v.removable || (depth && v.seen)) return true;
  if (!v.reason || v.poison || v.level == level) return false;
  const Level & l = control[v.level];
  if (!depth && l.seen < 2) return false;
  if (v.trail <= l.trail) return false;
  if (depth > opts.minimizedepth) return false;
  const int size = v.reason->size, * lits = v.reason->literals;
  bool res = true;
  for (int i = 0, other; res && i < size; i++)
    if ((other = lits[i]) != lit)
      res = minimize_literal (-other, depth+1);
  if (res) v.removable = true; else v.poison = true;
  minimized.push_back (lit);
  if (!depth) LOG ("minimizing %d %s", lit, res ? "succeeded" : "failed");
  return res;
}

// We try to minimize the first UIP clause by trying to remove away literals
// on smaller decision level first.  This makes more room for depth bounded
// minimization even though we have not really seen cases where the depth
// limit is hit and results in substantially less succesful minimization.

struct trail_smaller_than {
  Internal * internal;
  trail_smaller_than (Internal * s) : internal (s) { }
  bool operator () (int a, int b) {
    return internal->var (a).trail < internal->var (b).trail;
  }
};

void Internal::minimize_clause () {
  if (!opts.minimize) return;
  START (minimize);
  sort (clause.begin (), clause.end (), trail_smaller_than (this));
  LOG (clause, "minimizing first UIP clause");
  assert (minimized.empty ());
  stats.literals.learned += clause.size ();
  size_t j = 0;
  for (size_t i = 0; i < clause.size (); i++)
    if (minimize_literal (-clause[i])) stats.literals.minimized++;
    else clause[j++] = clause[i];
  LOG ("minimized %d literals", clause.size () - j);
  clause.resize (j);
  for (size_t i = 0; i < minimized.size (); i++) {
    Var & v = var (minimized[i]);
    v.removable = v.poison = false;
  }
  minimized.clear ();
  STOP (minimize);
  check_clause ();
}

};
