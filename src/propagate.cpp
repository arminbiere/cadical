#include "solver.hpp"

namespace CaDiCaL {

void Solver::assign (int lit, Clause * reason) {
  int idx = vidx (lit);
  assert (!vals[idx]);
  Var & v = vars[idx];
  if (!(v.level = level)) learn_unit_clause (lit);
  v.reason = reason;
  vals[idx] = phases[idx] = sign (lit);
  assert (val (lit) > 0);
  v.trail = (int) trail.size ();
  trail.push_back (lit);
  LOG (reason, "assign %d", lit);
}

/*------------------------------------------------------------------------*/

// The 'propagate' function is usually the hot-spot of a CDCL SAT solver.
// The 'trail' stack saves assigned variables and is used here as BFS queue
// for checking clauses with the negation of assigned variables for being in
// conflict or whether they produce additional assignments (units).  This
// version of 'propagate' uses lazy watches and keeps two watches literals
// at the beginning of the clause.  We also have seperate data structures
// for binary clauses and use 'blocking literals' to reduce the number of
// times clauses have to be visited.

bool Solver::propagate () {
  assert (!unsat);
  START (propagate);

  // The number of assigned variables propagated (at least for binary
  // clauses) gives the number of 'propagations', which is commonly used
  // to compare raw 'propagation speed' of solvers.  We save the BFS next
  // binary counter to avoid updating the 64-bit 'propagations' counter in
  // this tight loop below.

  const size_t before = next.binaries;

  while (!conflict) {

    // Propagate binary clauses eagerly and even continue propagating if a
    // conflicting binary clause is found.

    while (next.binaries < trail.size ()) {
      const int lit = trail[next.binaries++];
      LOG ("propagating binaries of %d", lit);
      assert (val (lit) > 0);
      assert (literal.binaries);
      const Watches & ws = binaries (-lit);
      for (size_t i = 0; i < ws.size (); i++) {
        const Watch & w = ws[i];
        const int other = w.blit, b = val (other);
        if (b < 0) conflict = w.clause;
        else if (!b) assign (other, w.clause);
      }
    }

    // Then if all binary clauses are propagated, go over longer clauses
    // with the negation of the assigned literal on the trail.

    if (!conflict && next.watches < trail.size ()) {
      const int lit = trail[next.watches++];
      assert (val (lit) > 0);
      LOG ("propagating watches of %d", lit);
      Watches & ws = watches (-lit);
      size_t i = 0, j = 0;
      while (i < ws.size ()) {
        const Watch w = ws[j++] = ws[i++];      // keep watch by default
        const int b = val (w.blit);
        if (b > 0) continue;
        Clause * c = w.clause;
        const int size = c->size;
        int * lits = c->literals;
        if (lits[1] != -lit) swap (lits[0], lits[1]);
        assert (lits[1] == -lit);
        const int u = val (lits[0]);
        if (u > 0) ws[j-1].blit = lits[0];
        else {
          int k, v = -1;
          for (k = 2; k < size && (v = val (lits[k])) < 0; k++)
            ;
          if (v > 0) ws[j-1].blit = lits[k];
          else if (!v) {
            LOG (c, "unwatch %d in", -lit);
            swap (lits[1], lits[k]);
            watch_literal (lits[1], -lit, c);
            j--;                                // flush watch
          } else if (!u) assign (lits[0], c);
          else { conflict = c; break; }
        }
      }
      while (i < ws.size ()) ws[j++] = ws[i++];
      ws.resize (j);

    } else break;
  }

  if (conflict) { stats.conflicts++; LOG (conflict, "conflict"); }
  stats.propagations += next.binaries - before;;

  STOP (propagate);
  return !conflict;
}


};
