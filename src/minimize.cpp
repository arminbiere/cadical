#include "internal.hpp"

namespace CaDiCaL {

// Functions for learned clause minimization. We only have the recursive
// version, which actually really is implemented recursively.  We also
// played with a derecursified version, which however was more complex and
// slower.  The trick to keep potential stack exhausting recursion under
// guards is to explicitly limit the recursion depth.

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
  if (!depth && l.seen.count < 2) return false;   // Don Knuth's idea
  if (v.trail <= l.seen.trail) return false;      // new early abort
  if (depth > opts.minimizedepth) return false;
  bool res = true;
  assert (v.reason);
  const const_literal_iterator end = v.reason->end ();
  const_literal_iterator i;
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
// help minimizing required recursion depth.  This might have the potential
// to simplify the algorithm too, but we still have to check that this has
// any effect in practice.  It clearly seems not harmful, and learned
// clauses have to be sorted anyhow.

struct minimize_trail_positive_rank {
  Internal * internal;
  minimize_trail_positive_rank (Internal * s) : internal (s) { }
  int operator () (const int & a) const {
    assert (internal->val (a));
    return internal->var (a).trail;
  }
};

struct minimize_trail_smaller {
  Internal * internal;
  minimize_trail_smaller (Internal * s) : internal (s) { }
  bool operator () (const int & a, const int & b) const {
    return internal->var (a).trail < internal->var (b).trail;
  }
};

void Internal::minimize_clause () {
  START (minimize);
  LOG (clause, "minimizing first UIP clause");

  external->check_learned_clause (); // check 1st UIP learned clause first

  // Sort the literals heuristically along assignment order with the hope to
  // hit the recursion limit 'opts.minimizedepth' less frequently.
  //
  MSORT (opts.radixsortlim,
    clause.begin (), clause.end (),
    minimize_trail_positive_rank (this), minimize_trail_smaller (this));

  assert (minimized.empty ());
  const auto end = clause.end ();
  auto j = clause.begin (), i = j;
  for (; i != end; i++)
    if (minimize_literal (-*i)) stats.minimized++;
    else flags (*j++ = *i).keep = true;
  LOG ("minimized %zd literals", (size_t)(clause.end () - j));
  if (j != end) clause.resize (j - clause.begin ());
  clear_minimized_literals ();
  STOP (minimize);
}

void Internal::clear_minimized_literals () {
  LOG ("clearing %zd minimized literals", minimized.size ());
  for (const auto & lit : minimized) {
    Flags & f = flags (lit);
    f.poison = f.removable = false;
  }
  for (const auto & lit : clause)
    flags (lit).keep = false;
  minimized.clear ();
}

}
