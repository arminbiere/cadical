#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Covered clause elimination (CCE) as described in our short LPAR-10 paper
// and later in more detail in our JAIR'15 article.  This implementation
// provides a simplified version of the one implemented in Lingeling. We
// still follow quite closely the original description, which is based on
// asymmetric literal addition (ALA) and covered literal addition (CLA).
// Both can be seen as kind of propagation, where the clauses in the
// original and then extended clause are assigned to false, and the literals
// on the trail (actually we use our own 'added' stack for that) make up the
// extended clause.   The ALA steps can be implemented by simple propagation
// (copied from 'propagate.cpp') using watches, while the CLA steps need
// full occurrence lists to determine the resolution candidate clauses.  The
// CCE is successful if a conflict is found during ALA steps or if during
// a CLA step all resolution candidates of a literal on the trail are
// satisfied (the extended clause is blocked).

struct Coveror {
  std::vector<int> added;               // acts as trail
  std::vector<int> clause;              // copy of the candidate clause
  std::vector<int> extend;              // extension stack for witness
  std::vector<int> covered;             // literals added through CLA
  std::vector<int> intersection;        // of literals in resolution cands

  struct { size_t asymmetric, covered; } next;  // propagate next ...

  Coveror () { next.asymmetric = next.covered = 0; }
};

/*------------------------------------------------------------------------*/

// Push on the extension stack a clause made up of the given literal, the
// original clause and all the added covered literals so far.  The given
// literal will act as blocking literal for that clause, if CCE is
// successful.  Only in this case, this private extension stack is copied to
// the actual extension stack of the solver.

inline void
Internal::cover_push_extension (int lit, Coveror & coveror) {
  coveror.extend.push_back (0);
  coveror.extend.push_back (lit);
  bool found = false;
  for (const auto & other : coveror.clause)
    if (lit == other) assert (!found), found = true;
    else coveror.extend.push_back (other);
  for (const auto & other : coveror.covered)
    if (lit == other) assert (!found), found = true;
    else coveror.extend.push_back (other);
  assert (found);
  (void) found;
}

// Successful CLA step.

inline void
Internal::covered_literal_addition (int lit, Coveror & coveror) {
  require_mode (COVER);
  assert (level == 1);
  cover_push_extension (lit, coveror);
  for (const auto & other : coveror.intersection) {
    LOG ("covered literal addition %d", other);
    assert (!vals[other]), assert (!vals[-other]);
    vals[other] = -1, vals[-other] = 1;
    coveror.covered.push_back (other);
    coveror.added.push_back (other);
  }
}

// Successful ALA step.

inline void
Internal::asymmetric_literal_addition (int lit, Coveror & coveror)
{
  require_mode (COVER);
  assert (level == 1);
  LOG ("initial asymmetric literal addition %d", lit);
  assert (!vals[lit]), assert (!vals[-lit]);
  vals[lit] = -1, vals[-lit] = 1;
  coveror.added.push_back (lit);
}

/*------------------------------------------------------------------------*/

// In essence copied and adapted from 'propagate' in 'propagate.cpp'. Since
// this function is also a hot-spot here in 'cover' we specialize it here
// (in the same spirit as 'probe_propagate' and 'vivify_propagate').  Please
// refer to the detailed comments for 'propagate' for explanations.

bool
Internal::cover_propagate_asymmetric (int lit,
                                      Clause * ignore,
                                      Coveror & coveror)
{
  require_mode (COVER);
  stats.propagations.cover++;
  assert (val (lit) < 0);
  bool subsumed = false;
  LOG ("asymmetric literal propagation of %d", lit);
  Watches & ws = watches (lit);
  const const_watch_iterator eow = ws.end ();
  watch_iterator j = ws.begin ();
  const_watch_iterator i = j;
  while (!subsumed && i != eow) {
    const Watch w = *j++ = *i++;
    if (w.clause == ignore) continue;   // costly but necessary here ...
    const int b = val (w.blit);
    if (b > 0) continue;
    if (w.clause->garbage) j--;
    else if (w.binary ()) {
      if (b < 0) {
        LOG (w.clause, "found subsuming");
        subsumed = true;
      } else asymmetric_literal_addition (-w.blit, coveror);
    } else {
      literal_iterator lits = w.clause->begin ();
      const int other = lits[0]^lits[1]^lit;
      lits[0] = other, lits[1] = lit;
      const int u = val (other);
      if (u > 0) j[-1].blit = other;
      else {
        const int size = w.clause->size;
        const const_literal_iterator end = lits + size;
        const literal_iterator middle = lits + w.clause->pos;
        literal_iterator k = middle;
        int v = -1, r = 0;
        while (k != end && (v = val (r = *k)) < 0)
          k++;
        if (v < 0) {
          k = lits + 2;
          assert (w.clause->pos <= size);
          while (k != middle && (v = val (r = *k)) < 0)
            k++;
        }
        w.clause->pos = k - lits;
        assert (lits + 2 <= k), assert (k <= w.clause->end ());
        if (v > 0) j[-1].blit = r;
        else if (!v) {
          LOG (w.clause, "unwatch %d in", lit);
          lits[1] = r;
          *k = lit;
          watch_literal (r, lit, w.clause);
          j--;
        } else if (!u) {
          assert (v < 0);
          asymmetric_literal_addition (-other, coveror);
        } else {
          assert (u < 0), assert (v < 0);
          LOG (w.clause, "found subsuming");
          subsumed = true;
          break;
        }
      }
    }
  }
  if (j != i) {
    while (i != eow) *j++ = *i++;
    ws.resize (j - ws.begin ());
  }
  return subsumed;
}

// Covered literal addition (which needs full occurrence lists).  The
// function returns 'true' if the extended clause is blocked on 'lit.'

bool
Internal::cover_propagate_covered (int lit, Coveror & coveror)
{
  require_mode (COVER);

  assert (val (lit) < 0);
  if (frozen (lit)) {
    LOG ("no covered propagating on frozen literal %d", lit);
    return false;
  }

  stats.propagations.cover++;

  LOG ("covered propagation of %d", lit);
  assert (coveror.intersection.empty ());

  Occs & os = occs (-lit);
  const auto end = os.end ();
  bool first = true;

  // Compute the intersection of the literals in all the clauses with
  // '-lit'.  If all these clauses are already satisfied then we know that
  // the extended clauses (in 'added') is blocked.  All literals in the
  // intersection can be added as covered literal. As soon the intersection
  // becomes empty (during traversal of clauses with '-lit') we abort.

  for (auto i = os.begin (); i != end; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    bool blocked = false;
    for (const auto & other : *c) {
      if (other == -lit) continue;
      int tmp = val (other);
      if (tmp < 0) continue;
      if (tmp > 0) { blocked = true; break; }
      if (first) {                              // copy & mark first
        coveror.intersection.push_back (other);
        mark (other);
      } else {                                  // unmark latter
        tmp = marked (other);
        if (tmp > 0) unmark (other);
      }
    }
    if (blocked) {                      // ... if 'c' is satisfied.
      LOG (c, "blocked");
      unmark (coveror.intersection);
      coveror.intersection.clear ();
      continue;                         // with next clause with '-lit'.
    }

    if (first) first = false;           // first clause copied and marked
    else {
      const auto end = coveror.intersection.end ();
      auto j = coveror.intersection.begin ();
      for (auto i = j; i != end; i++) {
        const int other = *j++ = *i;
        const int tmp = marked (other);
        assert (tmp >= 0);
        if (tmp) j--, unmark (other);   // remove marked and unmark it
        else mark (other);              // keep unmarked and mark it
      }
      const size_t new_size = j - coveror.intersection.begin ();
      coveror.intersection.resize (new_size);
    }

    if (coveror.intersection.empty ()) {  // no CLA candidates left ...
      auto begin = os.begin ();
      while (i != begin) {
        auto prev = i - 1;
        *i = *prev;
        i = prev;
      }
      *begin = c;
      break;                    // early abort ...
    }
  }

  bool res = false;
  if (first) {
    LOG ("all resolution candidates with %d blocked", -lit);
    cover_push_extension (lit, coveror);
    res = true;
  } else if (coveror.intersection.empty ()) {
    LOG ("empty intersection of resolution candidate literals");
  } else {
    LOG (coveror.intersection,
      "non-empty intersection of resolution candidate literals");
    covered_literal_addition (lit, coveror);
    unmark (coveror.intersection);
    coveror.intersection.clear ();
  }

  unmark (coveror.intersection);
  coveror.intersection.clear ();

  return res;
}

/*------------------------------------------------------------------------*/

bool Internal::cover_clause (Clause * c, Coveror & coveror) {

  require_mode (COVER);
  assert (!c->garbage);

  LOG (c, "trying covered clauses elimination on");
  bool satisfied = false;
  for (const auto & lit : *c)
    if (val (lit) > 0)
      satisfied = true;

  if (satisfied) {
    LOG (c, "clause already satisfied");
    mark_garbage (c);
    return false;
  }

  assert (coveror.added.empty ());
  assert (coveror.extend.empty ());
  assert (coveror.clause.empty ());
  assert (coveror.covered.empty ());

  assert (!level);
  level = 1;
  LOG ("assuming literals of candidate clause");
  for (const auto & lit : *c)
    if (!val (lit))
      asymmetric_literal_addition (lit, coveror),
      coveror.clause.push_back (lit);

  bool tautological = false;
  coveror.next.asymmetric = coveror.next.covered = 0;

  while (!tautological) {
    if (coveror.next.asymmetric < coveror.added.size ()) {
      while (!tautological &&
        coveror.next.asymmetric < coveror.added.size ()) {
        int lit = coveror.added[coveror.next.asymmetric++];
        tautological = cover_propagate_asymmetric (lit, c, coveror);
      }
    } else if (coveror.next.covered < coveror.added.size ()) {
      int lit = coveror.added[coveror.next.covered++];
      tautological = cover_propagate_covered (lit, coveror);
    } else break;
  }

  if (tautological) {

    if (coveror.covered.empty ()) {
      stats.cover.asymmetric++;
      stats.cover.total++;
      LOG (c, "asymmetric tautological");
      mark_garbage (c);
    } else {
      stats.cover.blocked++;
      stats.cover.total++;
      LOG (c, "covered tautological");
      mark_garbage (c);
    }

    // Only copy extension stack if successful.

    int prev = INT_MIN;
    for (const auto & other : coveror.extend) {
      if (!prev) {
        external->push_zero_on_extension_stack ();
        external->push_witness_literal_on_extension_stack (other);
        external->push_zero_on_extension_stack ();
      }
      if (other)
        external->push_clause_literal_on_extension_stack (other);
      prev = other;
    }
  }

  // Backtrack and 'unassign' all literals.

  assert (level == 1);
  for (const auto & lit : coveror.added)
    vals[lit] = vals[-lit] = 0;
  level = 0;

  coveror.covered.clear ();
  coveror.extend.clear ();
  coveror.clause.clear ();
  coveror.added.clear ();

  return tautological;
}

/*------------------------------------------------------------------------*/

// Not yet tried and larger clauses are tried first.

struct clause_covered_or_smaller {
  bool operator () (const Clause * a, const Clause * b) {
    if (a->covered && !b->covered) return true;
    if (!a->covered && b->covered) return false;
    return a->size < b->size;
  }
};

int64_t Internal::cover_round () {

  if (unsat) return 0;

  init_watches ();
  connect_watches (true);     // irredundant watches only is enough

  int64_t delta = stats.propagations.search;
  delta *= 1e-3 * opts.coverreleff;
  if (delta < opts.covermineff) delta = opts.covermineff;
  if (delta > opts.covermaxeff) delta = opts.covermaxeff;
  delta = max (delta, ((int64_t) 2) * active ());

  PHASE ("cover", stats.cover.count,
    "covered clause elimination limit of %" PRId64 " propagations", delta);

  int64_t limit = stats.propagations.cover + delta;

  init_occs ();

  vector<Clause *> schedule;
  Coveror coveror;

  // First connect all clauses and find all not yet tried clauses.
  //
  int64_t untried = 0;
  //
  for (auto c : clauses) {
    assert (!c->frozen);
    if (c->garbage) continue;
    if (c->redundant) continue;
    bool satisfied = false, allfrozen = true;
    for (const auto & lit : *c)
      if (val (lit) > 0) { satisfied = true; break; }
      else if (allfrozen && !frozen (lit)) allfrozen = false;
    if (satisfied) { mark_garbage (c); continue; }
    if (allfrozen) { c->frozen = true; continue; }
    for (const auto & lit : *c)
      occs (lit).push_back (c);
    if (c->covered) continue;
    schedule.push_back (c);
    untried++;
  }

  if (schedule.empty ()) {

    PHASE ("cover", stats.cover.count,
      "no previously untried clause left");

    for (auto c : clauses) {
      if (c->garbage) continue;
      if (c->redundant) continue;
      if (c->frozen) { c->frozen = false; continue; }
      assert (c->covered);
      c->covered = false;
      schedule.push_back (c);
    }
  } else {      // Mix of tried and not tried clauses ....

    for (auto c : clauses) {
      if (c->garbage) continue;
      if (c->redundant) continue;
      if (c->frozen) { c->frozen = false; continue; }
      if (!c->covered) continue;
      schedule.push_back (c);
    }
  }

  stable_sort (schedule.begin (), schedule.end (),
    clause_covered_or_smaller ());

#ifndef QUIET
  const size_t scheduled = schedule.size ();
  PHASE ("cover", stats.cover.count,
    "scheduled %zd clauses %.0f%% with %zd untried %.0f%%",
    scheduled, percent (scheduled, stats.current.irredundant),
    untried, percent (untried, scheduled));
#endif

  // Heuristically it should be beneficial to intersect with smaller clauses
  // first, since then the chances are higher that the intersection of
  // resolution candidates becomes emptier earlier.

  for (int idx = 1; idx <= max_var; idx++) {
    if (!active (idx)) continue;
    for (int sign = -1; sign <= 1; sign += 2) {
      const int lit = sign * idx;
      Occs & os = occs (lit);
      stable_sort (os.begin (), os.end (), clause_smaller_size ());
    }
  }

  // This is the main loop of trying to do CCE of candidate clauses.
  //
  int64_t covered = 0;
  //
  while (!terminating () &&
         !schedule.empty () &&
         stats.propagations.cover < limit) {
    Clause * c = schedule.back ();
    schedule.pop_back ();
    c->covered = true;
    if (cover_clause (c, coveror)) covered++;
  }

#ifndef QUIET
  const size_t remain = schedule.size ();
  const size_t tried = scheduled - remain;
  PHASE ("cover", stats.cover.count,
    "eliminated %" PRId64 " covered clauses out of %zd tried %.0f%%",
    covered, tried, percent (covered, tried));
  if (remain)
    PHASE ("cover", stats.cover.count,
      "remaining %" PRId64 " clauses %.0f%% untried",
      remain, percent (remain, scheduled));
  else
    PHASE ("cover", stats.cover.count,
      "all scheduled clauses tried");
#endif
  reset_occs ();
  reset_watches ();

  return covered;
}

/*------------------------------------------------------------------------*/

bool Internal::cover () {

  if (!opts.cover) return false;
  if (unsat || terminating () || !stats.current.irredundant) return false;

  // TODO: Our current algorithm for producing the necessary clauses on the
  // reconstruction stack for extending the witness requires a covered
  // literal addition step which (empirically) conflicts with flushing
  // during restoring clauses (see 'regr00{48,51}.trace') even though
  // flushing during restore is disabled by default (as is covered clause
  // elimination).  The consequence of combining these two options
  // ('opts.cover' and 'opts.restoreflush') can thus produce incorrect
  // witness reconstruction and thus invalid witnesses.  This is quite
  // infrequent (one out of half billion mobical test cases) but as the two
  // regression traces show, does happen. Thus we disable the combination.
  //
  if (opts.restoreflush) return false;

  START_SIMPLIFIER (cover, COVER);

  stats.cover.count++;

  // During variable elimination unit clauses can be generated which need to
  // be propagated properly over redundant clauses too.  Since variable
  // elimination avoids to have occurrence lists and watches at the same
  // time this propagation is delayed until the end of variable elimination.
  // Since we want to interleave CCE with it, we have to propagate here.
  // Otherwise this triggers inconsistencies.
  //
  if (propagated < trail.size ()) {
    init_watches ();
    connect_watches ();         // need to propagated over all clauses!
    LOG ("elimination produced %" PRId64 " units", trail.size () - propagated);
    if (!propagate ()) {
      LOG ("propagating units before covered clause elimination "
        "results in empty clause");
      learn_empty_clause ();
      assert (unsat);
    }
    reset_watches ();
  }
  assert (unsat || propagated == trail.size ());

  int64_t covered = cover_round ();

  STOP_SIMPLIFIER (cover, COVER);
  report ('c', !opts.reportall && !covered);

  return covered;
}

}
