#include "clause.hpp"
#include "internal.hpp"
#include "iterator.hpp"
#include "macros.hpp"
#include "util.hpp"

namespace CaDiCaL {

inline void Internal::search_assign (int lit, Clause * reason) {

  assert (!simplifying || vivifying);

  int idx = vidx (lit);

  assert (!vals[idx]);
  assert (!flags (idx).eliminated () || !reason);

  Var & v = var (idx);
  v.level = level;
  v.trail = (int) trail.size ();
  v.reason = reason;

  if (!level) learn_unit_clause (lit);   // increases 'stats.fixed'

  const signed char tmp = sign (lit);
  vals[idx] = tmp;
  vals[-idx] = -tmp;
  assert (val (lit) > 0);
  assert (val (-lit) < 0);
  phases[idx] = tmp;                     // phase saving during search

  propfixed (lit) = stats.fixed;         // avoids too much probing

  trail.push_back (lit);
  LOG (reason, "assign %d", lit);

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
// used to assign unit clauses on the root-level, in 'decide' to assign a
// decision or in 'analyze' to assign literal "driven" by a learned clause.
// This happens far less frequently than the 'search_assign' above, which
// is called directly in 'propagate' below.

void Internal::assign_unit (int lit) {
  assert (!level);
  search_assign (lit, 0);
}

void Internal::assign_decision (int lit) {
  assert (level > 0);
  assert (propagated == trail.size ());
  search_assign (lit, 0);
}

void Internal::assign_driving (int lit, Clause * c) {
  assert (c);
  search_assign (lit, c);
}

/*------------------------------------------------------------------------*/

// The 'propagate' function is usually the hot-spot of a CDCL SAT solver.
// The 'trail' stack saves assigned variables and is used here as BFS queue
// for checking clauses with the negation of assigned variables for being in
// conflict or whether they produce additional assignments (units).

// This version of 'propagate' uses lazy watches and keeps two watched
// literals at the beginning of the clause.  We also use 'blocking literals'
// to reduce the number of times clauses have to be visited (2008 JSAT paper
// by Chu, Harwood and Stuckey).  The watches know if a watched clause is
// binary, in which case it never hast to be visited.  If a binary clause is
// falsified we continue propagating.

// Finally, for long clauses we save the position of the last watch
// replacement in 'pos', which in turn reduces certain quadratic accumulated
// propagation costs (2013 JAIR article by Ian Gent) at the expense of four
// more bytes for long clauses (where it does not matter much).

bool Internal::propagate () {

  assert (!simplifying || vivifying);
  assert (!unsat);

  START (propagate);

  // Updating the statistics counter in the propagation loops is costly so
  // we delay until propagation run to completion.
  //
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

      if (b > 0) continue;                // blocking literal satisfied?

      if (w.binary) {

        // Binary clauses are treated separately since they do not require
        // to access the clause at all (only during conflict analysis, and
        // there also only to simplify the code).

        if (b < 0) conflict = w.clause;          // but continue ...
        else search_assign (w.blit, w.clause);

      } else {

        // The first pointer access to a long (non-binary) clause is the
        // most expensive operation in a CDCL SAT solver.  We count this by
        // the 'visits' counter.  However, since this would be in the
        // tightest loop of the solver, we only want to count it if
        // expensive statistics are required (actually costs quite a bit
        // having this enabled all the time).

        EXPENSIVE_STATS_ADD (visits, 1);

        if (w.clause->garbage) continue;
	if (w.clause->ignore) continue;

        literal_iterator lits = w.clause->begin ();

        // Simplify the code by assuming 'lit' is first literal in clause.
        // This is also implemented in MiniSAT.
        //
        if (lits[0] == lit) swap (lits[0], lits[1]);
        assert (lits[1] == lit);

        const int u = val (lits[0]);      // value of the other watch

        if (u > 0) j[-1].blit = lits[0];  // satisfied, just replace blit
        else {

          const int size = w.clause->size;
          const const_literal_iterator end = lits + size;
          const bool have_pos = w.clause->have_pos;
          literal_iterator k;
          int v = -1;

          // Now try to find a replacement watch.

          // This follows Ian Gent's idea of saving the position of the last
          // watch replacement.  In essence it needs two copies of the
          // default search for a watch replacement (in essence the code in
          // the 'else' branch below), one starting at the saved position
          // until the end of the clause and then if that one failed to find
          // a replacement another one starting at the first non-watched
          // literal until the saved position.

          // For shorter clauses of say size 3 (see 'opts.posize'), we do
          // not save the position and actually do not even have the memory
          // allocated for the '_pos' field in a clause.  For those we
          // simply start at the first unwatched literal.

          literal_iterator start = lits;
          start += have_pos ? w.clause->pos () : 2;

          k = start;
          while (k != end && (v = val (*k)) < 0) k++;

          EXPENSIVE_STATS_ADD (traversed, k - start);

          if (have_pos) {

            if (v < 0) {  // need second search starting at the head?

              const const_literal_iterator middle = lits + w.clause->pos ();
              k = lits + 2;
              assert (w.clause->pos () <= size);
              while (k != middle && (v = val (*k)) < 0) k++;

              EXPENSIVE_STATS_ADD (traversed, k - (lits + 2));
            }

            w.clause->pos () = k - lits;  // always save position
          }

          assert (lits + 2 <= k), assert (k <= w.clause->end ());

          if (v > 0) j[-1].blit = *k;    // satisfied, just replace 'blit'
          else if (!v) {

            // Found new unassigned replacement literal to be watched.

            LOG (w.clause, "unwatch %d in", *k);

            swap (lits[1], *k);
            watch_literal (lits[1], lit, w.clause, size);

            j--;  // drop this watch from the watch list of 'lit'

          } else if (!u) {

            assert (v < 0);

            // The other watch is unassigned ('!u') and all other literals
            // assigned to false (still 'v < 0'), thus we found a unit.
            //
            search_assign (lits[0], w.clause);

          } else {

            assert (u < 0);
            assert (v < 0);

            // The other watch is assigned false ('u < 0') and all other
            // literals as well (still 'v < 0'), thus we found a conflict.

            conflict = w.clause;
            break;                       // (*)
          }
        }
      }
    }
    while (i != ws.end ()) *j++ = *i++;  // because of the 'break' at (*)
    ws.resize (j - ws.begin ());
  }
  long delta = propagated - before;
  if (vivifying) stats.propagations.vivify += delta;
  else stats.propagations.search += delta;
  if (conflict) {
    if (!vivifying) stats.conflicts++;
    LOG (conflict, "conflict");
  }
  STOP (propagate);
  return !conflict;
}

};
