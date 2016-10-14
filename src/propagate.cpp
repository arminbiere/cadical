#include "internal.hpp"

namespace CaDiCaL {

void Internal::assign (int lit, Clause * reason) {
  int idx = vidx (lit);
  assert (!vals[idx]);
  Var & v = var (idx);
  if (!(v.level = level)) learn_unit_clause (lit);
  v.reason = reason;
  vals[idx] = phases[idx] = sign (lit);
  assert (val (lit) > 0);
  v.trail = (int) trail.size ();
  trail.push_back (lit);
  LOG (reason, "assign %d", lit);
}

// The 'propagate' function is usually the hot-spot of a CDCL SAT solver.
// The 'trail' stack saves assigned variables and is used here as BFS queue
// for checking clauses with the negation of assigned variables for being in
// conflict or whether they produce additional assignments (units).  This
// version of 'propagate' uses lazy watches and keeps two watches literals
// at the beginning of the clause.  We also use 'blocking literals' to
// reduce the number of times clauses have to be visited.

bool Internal::propagate () {
  assert (!unsat);
  START (propagate);
  while (!conflict && propagated < trail.size ()) {
    stats.propagations++;
    const int lit = -trail[propagated++];
    LOG ("propagating %d", -lit);
    Watches & ws = watches (lit);
    const_watch_iterator i = ws.begin ();
    watch_iterator j = ws.begin ();
    while (i != ws.end ()) {
      const Watch w = *j++ = *i++;
      const int b = val (w.blit);
      if (b > 0) continue;
      if (w.size == 2) {
        if (b < 0) conflict = w.clause;
        else if (!b) assign (w.blit, w.clause);
      } else {
        int * lits = w.clause->literals;
        if (lits[0] == lit) swap (lits[0], lits[1]);
        const int u = val (lits[0]);
        if (u > 0) j[-1].blit = lits[0];
        else {
          int k, v = -1;
          for (k = 2; k < w.size && (v = val (lits[k])) < 0; k++)
            ;
          if (v > 0) j[-1].blit = lits[k];
          else if (!v) {
            LOG (c, "unwatch %d in", lit);
	    swap (lits[1], lits[k]);
            watch_literal (lits[1], lit, w.clause, w.size);
            j--;
          } else if (!u) assign (lits[0], w.clause);
          else { conflict = w.clause; break; }
        }
      }
    }
    while (i != ws.end ()) *j++ = *i++;
    ws.resize (j - ws.begin ());
  }
  if (conflict) { stats.conflicts++; LOG (conflict, "conflict"); }
  STOP (propagate);
  return !conflict;
}

};
