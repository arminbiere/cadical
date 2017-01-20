#include "internal.hpp"

namespace CaDiCaL {

// Functions for learned clause minimization. We only have the recursive
// version, which actually is implemented recursively.  We also played with
// a non-recursive version, which however was more complex and slower.  The
// trick to keep potential stack exhausting recursion under guards is to
// explicitly limit the recursion depth.

// Instead of signatures as in the original implementation in MiniSAT and
// our corresponding paper, we use the 'poison' idea of Allen Van Gelder to
// mark unsuccessful removal attempts, then Donald Knuth's idea to abort
// minimization if only one literal was seen on the level and a new idea of
// also aborting if the earliest seen literal was assigned afterwards.

bool Internal::minimize_literal (int lit, int depth) {
  Flags & f = flags (lit);
  Var & v = var (lit);
  if (!v.level || f.removable || f.keep) return true;
  if (!v.reason || f.poison || v.level == level) return false;
  const Level & l = control[v.level];
  if (!depth && l.seen < 2) return false;         // Don Knuth's idea
  if (v.trail <= l.trail) return false;           // new early abort
  if (depth > opts.minimizedepth) return false;
  bool res = true;
  assert (v.reason);
  const_literal_iterator end = v.reason->end (), i;
  for (i = v.reason->begin (); res && i != end; i++) {
    const int other = *i;
    if (other == lit) continue;
    res = minimize_literal (-other, depth + 1);
  }
  if (res) f.removable = true; else f.poison = true;
  minimized.push_back (lit);
  if (!depth) LOG ("minimizing %d %s", lit, res ? "succeeded" : "failed");
  return res;
}

// Sorting the clause before minimization with respect to the trail order
// (literals with smaller trail height first) seems to be natural and could
// help minimizing required recursion depth.   It might simplify the
// algorithm too, but we still have to check that this as any effect in
// practice (TODO).

struct trail_assigned_smaller {
  Internal * internal;
  trail_assigned_smaller (Internal * s) : internal (s) { }
  bool operator () (int a, int b) {
    assert (internal->val (a)), assert (internal->val (b));
    return internal->var (a).trail < internal->var (b).trail;
  }
};

void Internal::minimize_clause () {
  START (minimize);
  LOG (clause, "minimizing first UIP clause");
  sort (clause.begin (), clause.end (), trail_assigned_smaller (this));
  assert (minimized.empty ());
  int_iterator j = clause.begin ();
  for (const_int_iterator i = j; i != clause.end (); i++)
    if (minimize_literal (-*i)) stats.minimized++;
    else flags (*j++ = *i).keep = true;
  LOG ("minimized %d literals", (long)(clause.end () - j));
  clause.resize (j - clause.begin ());
  clear_minimized ();
  external->check_learned_clause ();
  STOP (minimize);
}

void Internal::clear_minimized () {
  const_int_iterator i;
  for (i = minimized.begin (); i != minimized.end (); i++) {
    Flags & f = flags (*i);
    f.poison = f.removable = false;
  }
  for (i = clause.begin (); i != clause.end (); i++)
    flags (*i).keep = false;
  minimized.clear ();
}

};
