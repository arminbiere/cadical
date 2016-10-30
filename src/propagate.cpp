#include "internal.hpp"

#include "clause.hpp"
#include "iterator.hpp"
#include "macros.hpp"
#include "util.hpp"

namespace CaDiCaL {

void Internal::assign (int lit, Clause * reason, int other) {
  int idx = vidx (lit);
  assert (!vals[idx]);
  Var & v = var (idx);
  v.level = level;
  v.other = other;
  v.reason = reason;
  if (!level) learn_unit_clause (lit);
  const signed char tmp = sign (lit);
  vals[idx] = phases[idx] = tmp;
  vals[-idx] = -tmp;
  assert (val (lit) > 0);
  trail.push_back (lit);
#ifdef LOGGING
  if (other) LOG ("assign %d binary reason %d %d", lit, lit, other);
  else LOG (reason, "assign %d", lit);
#endif
  // As 'assign' is called most of the time from 'propagate' below and then
  // the watches of '-lit' are accessed next during propagation it is wise
  // to tell the processor to prefetch the memory of those watches.  This
  // seems to give consistent speed-ups (both with 'g++' and 'clang++') in
  // the order of 5%.  Even though this is a rather low-level optimization
  // it is confined to the next line (and these comments), so we keep it.
  //
  if (opts.prefetch) __builtin_prefetch (&*(watches (-lit).begin ()), 1);
}

// The 'propagate' function is usually the hot-spot of a CDCL SAT solver.
// The 'trail' stack saves assigned variables and is used here as BFS queue
// for checking clauses with the negation of assigned variables for being in
// conflict or whether they produce additional assignments (units).  This
// version of 'propagate' uses lazy watches and keeps two watched literals
// at the beginning of the clause.  We also use 'blocking literals' to
// reduce the number of times clauses have to be visited.  The watches know
// if a watched clause is binary, in which case it never hast to be visited.
// If a binary clause is falsified we continue propagating.

bool Internal::propagate () {
  assert (!unsat);
  START (propagate);
  long before = propagated;
  while (!conflict && propagated < trail.size ()) {
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
        else if (!b) assign (w.blit, 0, lit);
      } else {
        literal_iterator lits = w.clause->begin ();
        if (lits[0] == lit) swap (lits[0], lits[1]);
        const int u = val (lits[0]);
        if (u > 0) j[-1].blit = lits[0];
        else {
          const_literal_iterator end = lits + w.size;
          literal_iterator k = lits + 2;
          int v = -1;
          while (k != end && (v = val (*k)) < 0) k++;
          if (v > 0) j[-1].blit = *k;
          else if (!v) {
            LOG (w.clause, "unwatch %d in", *k);
            swap (lits[1], *k);
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
  stats.propagations += propagated - before;
  STOP (propagate);
  return !conflict;
}

};
