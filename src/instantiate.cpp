#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// This provides an implementation of variable instantiation, a technique
// for removing literals with few occurrence (see also 'instantiate.hpp').

/*------------------------------------------------------------------------*/

// Triggered at the end of a variable elimination round ('elim_round').

void
Internal::collect_instantiation_candidates (Instantiator & instantiator) {
  assert (occurring ());
  for (int idx = 1; idx <= max_var; idx++) {
    if (frozen (idx)) continue;
    if (!active (idx)) continue;
    if (flags (idx).elim) continue;               // BVE attempt pending
    for (int sign = -1; sign <= 1; sign += 2) {
      const int lit = sign * idx;
      if (noccs (lit) > opts.instantiateocclim) continue;
      Occs & os = occs (lit);
      for (const auto & c : os) {
        if (c->garbage) continue;
        if (opts.instantiateonce && c->instantiated) continue;
        if (c->size < opts.instantiateclslim) continue;
        bool satisfied = false;
        int unassigned = 0;
        for (const auto & other : *c) {
          const int tmp = val (other);
          if (tmp > 0) satisfied = true;
          if (!tmp) unassigned++;
        }
        if (satisfied) continue;
        if (unassigned < 3) continue;           // avoid learning units
        size_t negoccs = occs (-lit).size ();
        LOG (c,
          "instantiation candidate literal %d "
          "with %zd negative occurrences in");
        instantiator.candidate (lit, c, c->size, negoccs);
      }
    }
  }
}

/*------------------------------------------------------------------------*/

// Specialized propagation and assignment routines for instantiation.

inline void Internal::inst_assign (int lit) {
  LOG ("instantiate assign %d");
  assert (!val (lit));
  vals[lit] = 1;
  vals[-lit] = -1;
  trail.push_back (lit);
}

bool Internal::inst_propagate () {      // Adapted from 'propagate'.
  START (propagate);
  int64_t before = propagated;
  bool ok = true;
  while (ok && propagated != trail.size ()) {
    const int lit = -trail[propagated++];
    LOG ("instantiate propagating %d", -lit);
    Watches & ws = watches (lit);
    const const_watch_iterator eow = ws.end ();
    const_watch_iterator i = ws.begin ();
    watch_iterator j = ws.begin ();
    while (i != eow) {
      const Watch w = *j++ = *i++;
      const int b = val (w.blit);
      if (b > 0) continue;
      if (w.binary ()) {
        if (b < 0) { ok = false; LOG (w.clause, "conflict"); break; }
        else inst_assign (w.blit);
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
          if (v > 0) {
            j[-1].blit = r;
          } else if (!v) {
            LOG (w.clause, "unwatch %d in", r);
            lits[1] = r;
            *k = lit;
            watch_literal (r, lit, w.clause);
            j--;
          } else if (!u) {
            assert (v < 0);
            inst_assign (other);
          } else {
            assert (u < 0);
            assert (v < 0);
            LOG (w.clause, "conflict");
            ok = false;
            break;
          }
        }
      }
    }
    if (j != i) {
      while (i != eow)
        *j++ = *i++;
      ws.resize (j - ws.begin ());
    }
  }
  int64_t delta = propagated - before;
  stats.propagations.instantiate += delta;
  STOP (propagate);
  return ok;
}

/*------------------------------------------------------------------------*/

// This is the actual instantiation attempt.

bool Internal::instantiate_candidate (int lit, Clause * c) {
  stats.instried++;
  if (c->garbage) return false;
  assert (!level);
  bool found = false, satisfied = false, inactive = false;
  int unassigned = 0;
  for (const auto & other : *c) {
    if (other == lit) found = true;
    const int tmp = val (other);
    if (tmp > 0) { satisfied = true; break; }
    if (!tmp && !active (other)) { inactive = true; break; }
    if (!tmp) unassigned++;
  }
  if (!found) return false;
  if (inactive) return false;
  if (satisfied) return false;
  if (unassigned < 3) return false;
  size_t before = trail.size ();
  assert (propagated == before);
  assert (active (lit));
  LOG (c, "trying to instantiate %d in", lit);
  assert (!c->garbage);
  c->instantiated = true;
  level++;
  inst_assign (lit);                            // Assume 'lit' to true.
  for (const auto & other : *c) {
    if (other == lit) continue;
    const int tmp = val (other);
    if (tmp) { assert (tmp < 0); continue; }
    inst_assign (-other);                       // Assume other to false.
  }
  bool ok = inst_propagate ();                  // Propagate.
  while (trail.size () > before) {              // Backtrack.
    const int other = trail.back ();
    LOG ("instantiate unassign %d", other);
    trail.pop_back ();
    assert (val (other) > 0);
    vals[other] = vals[-other] = 0;
  }
  propagated = before;
  assert (level == 1);
  level = 0;
  if (ok) { LOG ("instantiation failed"); return false; }
  unwatch_clause (c);
  strengthen_clause (c, lit);
  watch_clause (c);
  assert (c->size > 1);
  LOG ("instantiation succeeded");
  stats.instantiated++;
  return true;
}

/*------------------------------------------------------------------------*/

// Try to instantiate all candidates collected before through the
// 'collect_instantiation_candidates' routine.

void Internal::instantiate (Instantiator & instantiator) {
  assert (opts.instantiate);
  START (instantiate);
  stats.instrounds++;
#ifndef QUIET
  const int64_t candidates = instantiator.candidates.size ();
#endif
  int64_t instantiated = 0, tried = 0;
  init_watches ();
  connect_watches ();
  if (propagated < trail.size ()) {
    if (!propagate ()) {
      LOG ("propagation after connecting watches failed");
      learn_empty_clause ();
      assert (unsat);
    }
  }
  PHASE ("instantiate", stats.instrounds,
    "attempting to instantiate %zd candidate literal clause pairs",
    candidates);
  while (!unsat &&
         !terminating () &&
         !instantiator.candidates.empty ()) {
    Instantiator::Candidate cand = instantiator.candidates.back ();
    instantiator.candidates.pop_back ();
    tried++;
    if (!active (cand.lit)) continue;
    LOG (cand.clause,
      "trying to instantiate %d with "
      "%zd negative occurrences in", cand.lit, cand.negoccs);
    if (!instantiate_candidate (cand.lit, cand.clause)) continue;
    instantiated++;
    VERBOSE (2, "instantiation %" PRId64 " (%.1f%%) succeeded (%.1f%%) with "
      "%zd negative occurrences in size %d clause",
      tried, percent (tried, candidates),
      percent (instantiated, tried), cand.negoccs, cand.size);
  }
  PHASE ("instantiate", stats.instrounds,
    "instantiated %" PRId64 " candidate successfully out of %" PRId64 " tried %.1f%%",
    instantiated, tried, percent (instantiated, tried));
  report ('I', !instantiated);
  reset_watches ();
  STOP (instantiate);
}

}
