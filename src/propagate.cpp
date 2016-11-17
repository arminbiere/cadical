#include "clause.hpp"
#include "internal.hpp"
#include "iterator.hpp"
#include "macros.hpp"
#include "util.hpp"

namespace CaDiCaL {

inline void Internal::assign (int lit, Clause * reason, int other) {
  int idx = vidx (lit);
  assert (!vals[idx]);
  assert (!etab[idx] || (!reason && !other));
  Var & v = var (idx);
  v.level = level;
  v.trail = (int) trail.size ();
  v.other = other;
  v.reason = reason;
  if (!level) learn_unit_clause (lit);
  const signed char tmp = sign (lit);
  vals[idx] = tmp;
  vals[-idx] = -tmp;
  if (!simplifying) phases[idx] = tmp;
  fixedprop (lit) = stats.fixed;
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
  // the order of 5%.  For instance on 'sokoban-p20.sas.ex.13', which has
  // very high propagation per conflict rates, we saw a difference of 24
  // seconds for the version with prefetching versus 32 seconds for the one
  // without. This was for the first 10k conflicts and resulted of course in
  // the same search space otherwise.  Even though this is a rather
  // low-level optimization it is confined to the next line (and these
  // comments), so we keep it.
  //
  if (opts.prefetch && watches ())
    __builtin_prefetch (&*(watches (-lit).begin ()));
}

/*------------------------------------------------------------------------*/

// External versions of 'assign' which are not inlined.  They either are
// used in 'decide' or in 'analyze' to assign a decision or a learned
// clause.  This happens far less frequently than the 'assign' above, which
// is only called from 'propagate' below (and thus can be inlined).

void Internal::assign (int lit) { assign (lit, 0, 0); }

void Internal::assign (int lit, Clause * c) { assign (lit, c, 0); }

/*------------------------------------------------------------------------*/

// The 'propagate' function is usually the hot-spot of a CDCL SAT solver.
// The 'trail' stack saves assigned variables and is used here as BFS queue
// for checking clauses with the negation of assigned variables for being in
// conflict or whether they produce additional assignments (units).  This
// version of 'propagate' uses lazy watches and keeps two watched literals
// at the beginning of the clause.  We also use 'blocking literals' to
// reduce the number of times clauses have to be visited (2008 JSAT paper by
// Chu, Harwood and Stuckey).  The watches know if a watched clause is
// binary, in which case it never hast to be visited.  If a binary clause is
// falsified we continue propagating.  Finally, we save the position of the
// last watch replacement in 'pos', which in turn reduces certain quadratic
// accumulated propagation costs (2013 JAIR article by Ian Gent) at the
// expense of four more bytes.

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
        EXPENSIVE_STATS_ADD (simplifying, visits, 1);
        if (w.clause->garbage) continue;
        literal_iterator lits = w.clause->begin ();
        if (lits[0] == lit) swap (lits[0], lits[1]);
        const int u = val (lits[0]);
        if (u > 0) j[-1].blit = lits[0];
        else {
          const const_literal_iterator end = lits + w.size;
          assert (w.size == w.clause->size);
          literal_iterator k = lits + w.clause->pos;
          int v = -1;
          while (k != end && (v = val (*k)) < 0) k++;
          EXPENSIVE_STATS_ADD (simplifying,
	    traversed, k - (lits + w.clause->pos));
          if (v < 0) {
            const const_literal_iterator middle = lits + w.clause->pos;
            k = lits + 2;
            assert (w.clause->pos <= w.size);
            while (k != middle && (v = val (*k)) < 0) k++;
            EXPENSIVE_STATS_ADD (simplifying,
	      traversed, k - (lits + 2));
          }
          assert (lits + 2 <= k), assert (k <= w.clause->end ());
          w.clause->pos = k - lits;
          if (v > 0) j[-1].blit = *k;
          else if (!v) {
            LOG (w.clause, "unwatch %d in", *k);
            swap (lits[1], *k);
            watch_literal (lits[1], lit, w.clause, w.size);
            j--;
          } else if (!u) assign (lits[0], w.clause, 0);
          else { conflict = w.clause; break; }
        }
      }
    }
    while (i != ws.end ()) *j++ = *i++;
    ws.resize (j - ws.begin ());
  }
  long delta = propagated - before;
  if (simplifying) stats.probagations += delta;
  else             stats.propagations += delta;
  //                        ^ !!!!!
  if (conflict) {
    if (!simplifying) stats.conflicts++; 
    LOG (conflict, "conflict");
  }
  STOP (propagate);
  return !conflict;
}

};
