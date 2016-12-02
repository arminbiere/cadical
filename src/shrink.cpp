#ifdef SHRINK

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
// to avoid cycles (which would yield unsound removals).

bool Internal::shrink_literal (int lit, int depth) {
  assert (val (lit) > 0);
  Flags & f = flags (lit);
  Var & v = var (lit);
  if (!v.level || f.removable || f.clause) return true;
  if (!v.reason || f.poison || v.level == level) return false;
  const Level & l = control[v.level];
  if (!depth && l.seen < 2) return false;
  if (v.trail <= l.trail) return false;
  if (depth > opts.shrinkdepth) return false;
  bool remove = false;
  Watches & ws = watches (lit);

  // The difference to 'minimize_literal' is here, where we iterate over all
  // clauses watches by 'lit' instead of 'just' the reason clause except for
  // '(!!!)' where we have to make sure that we respect assignment order in
  // resolutions to avoid cyclic derivations.  For the actual reason this
  // test is not necessary.

  const const_watch_iterator eow = ws.end ();
  const_watch_iterator i;
  for (i = ws.begin (); !remove && i != eow; i++) {
    Clause * c = i->clause;
    const const_literal_iterator eoc = c->end ();
    const_literal_iterator j;
    bool failed = false;
    int lit_trail = var (lit).trail;
    for (j = c->begin (); !failed && j != eoc; j++) {
      int other = *j;
      if (other == lit) continue;
      else if (val (other) >= 0) failed = true;
      else if (var (other).trail > lit_trail) failed = true;  // (!!!)
      else failed = !shrink_literal (-other, depth+1);
    }
    if (!failed) remove = true;
  }

  if (remove) f.removable = true; else f.poison = true;
  minimized.push_back (lit);
  if (!depth) LOG ("shrinking %d %s", lit, remove ? "succeeded" : "failed");
  return remove;
}

void Internal::shrink_clause () {
  START (shrink);
  LOG (clause, "shrinking minimized first UIP clause");
  stats.shrinktried += clause.size ();
  sort (clause.begin (), clause.end (), trail_smaller (this));
  assert (minimized.empty ());
  int_iterator j = clause.begin ();
  for (const_int_iterator i = j; i != clause.end (); i++)
    if (shrink_literal (-*i)) stats.shrunken++;
    else flags (*j++ = *i).clause = true;
  LOG ("shrunken %d literals", (long)(clause.end () - j));
  clause.resize (j - clause.begin ());
  clear_minimized ();
  check_learned_clause ();
  STOP (shrink);
}

};

#endif
