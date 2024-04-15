#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Hyper binary transmutation

// The following functions 'transmute_assign' and 'transmute_propagate' are used for
// propagating during failed literal probing in simplification mode, as
// replacement of the generic propagation routine 'propagate' and
// 'search_assign'.

// The code is mostly copied from 'probe.cpp'.
// LRAT will be a pain! code currently without.

inline void Internal::transmute_assign (int lit, clause *reason) {
  require_mode (TRANSMUTE);
  int idx = vidx (lit);
  assert (!val (idx));
  Var &v = var (idx);
  v.level = level;
  v.trail = (int) trail.size ();
  assert ((int) num_assigned < max_var);
  num_assigned++;
  v.reason = level ? reason : 0;
  if (!level)
    learn_unit_clause (lit);
  else
    assert (level == 1);
  const signed char tmp = sign (lit);
  set_val (idx, tmp);
  assert (val (lit) > 0);
  assert (val (-lit) < 0);
  trail.push_back (lit);
}

void Internal::transmute_assign_decision (int lit) {
  require_mode (TRANSMUTE);
  assert (!level);
  assert (propagated == trail.size ());
  level++;
  control.push_back (Level (lit, trail.size ()));
  transmute_assign (lit, 0);
}

void Internal::transmute_assign_unit (int lit) {
  require_mode (TRANSMUTE);
  assert (!level);
  assert (active (lit));
  transmute_assign (lit, 0);
}

/*------------------------------------------------------------------------*/


// This is essentially the same as 'propagate' except that we prioritize and
// always propagate binary clauses first (see our CPAIOR'13 paper on tree
// based look ahead), then immediately stop at a conflict and of course use
// 'probe_assign' instead of 'search_assign'.  The binary propagation part
// is factored out too.  If a new unit on decision level one is found we
// perform hyper binary resolution and thus actually build an implication
// tree instead of a DAG.  Statistics counters are also different.

inline void Internal::transmute_propagate2 () {
  require_mode (TRANSMUTE);
  while (propagated2 != trail.size ()) {
    const int lit = -trail[propagated2++];
    LOG ("probe propagating %d over binary clauses", -lit);
    Watches &ws = watches (lit);
    for (const auto &w : ws) {
      if (!w.binary ())
        continue;
      const signed char b = val (w.blit);
      if (b > 0)
        continue;
      if (b < 0)
        conflict = w.clause; // but continue
      else {
        assert (lrat_chain.empty ());
        assert (!probe_reason);
        probe_reason = w.clause;
        probe_lrat_for_units (w.blit);
        probe_assign (w.blit, -lit);
        lrat_chain.clear ();
      }
    }
  }
}

bool Internal::transmute_propagate () {
  require_mode (TRANSMUTE);
  assert (!unsat);
  START (propagate);
  int64_t before = propagated2 = propagated;
  while (!conflict) {
    if (propagated2 != trail.size ())
      probe_propagate2 ();
    else if (propagated != trail.size ()) {
      const int lit = -trail[propagated++];
      LOG ("probe propagating %d over large clauses", -lit);
      Watches &ws = watches (lit);
      size_t i = 0, p = 0;
      while (i != ws.size ()) {
        const Watch w = ws[p++] = ws[i++];
        if (w.binary ())
          continue;
        const signed char b = val (w.blit);
        if (b > 0)
          continue;
        if (w.clause->garbage)
          continue;
        const literal_iterator lits = w.clause->begin ();
        const int other = lits[0] ^ lits[1] ^ lit;
        // lits[0] = other, lits[1] = lit;
        const signed char u = val (other);
        if (u > 0)
          ws[p - 1].blit = other;
        else {
          const int size = w.clause->size;
          const const_literal_iterator end = lits + size;
          const literal_iterator middle = lits + w.clause->pos;
          literal_iterator k = middle;
          int r = 0;
          signed char v = -1;
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
          if (v > 0)
            ws[p - 1].blit = r;
          else if (!v) {
            LOG (w.clause, "unwatch %d in", r);
            *k = lit;
            lits[0] = other;
            lits[1] = r;
            watch_literal (r, lit, w.clause);
            p--;
          } else if (!u) {
            if (level == 1) {
              lits[0] = other, lits[1] = lit;
              assert (lrat_chain.empty ());
              assert (!probe_reason);
              int dom = hyper_binary_resolve (w.clause);
              probe_assign (other, dom);
            } else {
              assert (lrat_chain.empty ());
              assert (!probe_reason);
              probe_reason = w.clause;
              probe_lrat_for_units (other);
              probe_assign_unit (other);
              lrat_chain.clear ();
            }
            probe_propagate2 ();
          } else
            conflict = w.clause;
        }
      }
      if (p != i) {
        while (i != ws.size ())
          ws[p++] = ws[i++];
        ws.resize (p);
      }
    } else
      break;
  }
  int64_t delta = propagated2 - before;
  stats.propagations.probe += delta;
  if (conflict)
    LOG (conflict, "conflict");
  STOP (propagate);
  return !conflict;
}


/*------------------------------------------------------------------------*/

// We consider all clauses of size >= 4 and glue >= 2 for transmutation.
// Clauses bigger 64 are skipped in order to efficiently calculate set cover.
// However, clauses can only be candidates once.

bool Internal::consider_to_transmute_clause (Clause *c) {
  if (c->garbage)
    return false;
  if (c->glue < 2)
    return false;
  if (c->size < 4)
    return false;
  if (c->size > 64)
    return false;
  if (c->transmuted)
    return false;
  return true;
}

void Internal::transmute_clause (Transmuter &transmuter, Clause *c) {

  // at least length 4 glue 2 clauses
  assert (c->size > 3);
  assert (c->glue > 1);

  c->transmuted = true; // remember transmuted clauses

  if (c->garbage)
    return;

  // First check whether the candidate clause is already satisfied and at
  // the same time copy its non fixed literals to 'current'.
  //
  int satisfied = 0;
  auto &current = vivifier.current;
  current.clear ();

  for (const auto &lit : *c) {
    const int tmp = fixed (lit);
    if (tmp > 0) {
      satisfied = lit;
      break;
    } else if (!tmp)
      current.push_back (lit);
  }
  assert (current.size <= 64);

  if (satisfied) {
    LOG (c, "satisfied by propagated unit %d", satisfied);
    mark_garbage (c);
    return;
  } else if (current.size () < 4) {
    LOG (c, "too short after unit simplification");
    return;
  }

  // The actual transmutation checking is performed here, by probing
  // each of the literals of the clause.
  // The goal is to find two literals l, k, such that every literal c_i of
  // the clause either implies l or k. Furthermore, we only consider golden
  // pairs, i.e. neither l nor k imply more than n-2 literals in a clause of
  // size n. Thus the smalles candidate size for transmutation is 4.
  // Early abort happens when the clause becomes too short because of learnt units.
  
  LOG (c, "transmutation checking");
  stats.transmutechecks++;

  assert (!level);

  // we use vlit for indexing the covered array.
  vector<uint64_t> covered;
  covered.resize (max_var * 2 + 1);

  unsigned idx = 0;
  unsigned size = current.size ();
  const auto end = current.end ();
  auto p = current.begin ();
  auto q = p;

  // Go over the literals in the candidate clause.
  //
  while (q != end) {
    const auto &lit = *p++ = q++;
    idx++;
    assert (!conflict);
    if (val (lit) > 0) {
      LOG (c, "satisfied by propagated unit %d", lit);
      mark_garbage (c);
      return;
    } else if (val (lit) < 0) {
      LOG ("skipping falsified literal %d", lit);
      p--;
      idx--;
      size--;
      if (size < 4) {
        LOG (c, "too short after unit simplification");
        return;
      }
      continue;
    }
    
    stats.transmutedecs++;
    transmute_assume (lit);
    LOG ("decision %d score %" PRId64 "", lit, noccs (lit));

    // hot spot
    if (!transmute_propagate ()) {
      LOG ("learning %d and skipping now falsified %d", -lit, lit);
      backtrack (level - 1);
      conflict = 0;
      assert (!val (lit));
      transmute_assign_unit (-lit);
      p--;
      idx--;
      size--;
      if (!propagate ()) {
        LOG ("propagation after learning unit results in inconsistency");
        learn_empty_clause ();
      }
      if (size < 4) {
        LOG (c, "too short after unit simplification");
        return;
      }
      continue;
    }
    
    for (size_t begin = control[level].trail + 1; begin < trail.size (); begin++) {
      const auto & other = trail[begin];
      covered[vlit (other)] += (uint64_t) 1 << idx;  // mark other
    }

    backtrack (level - 1);

  }
  assert (size >= 4);
  if (p != q) {
    while (q != end)
      *p++ = *q++;

    current.resize (p - current.begin ());
  }
  assert (!conflict);

  // now we have to analyze 'covered' in order to find out if there are
  // a pair of literals that covers the clause in the above described way.
  // This is quadratic in the number of literals. To improve performance we
  // filter for candidates which cover at least two literals first.
  //
  vector<int> candidates;
  for (const auto & lit : lits) {
    if (__builtin_popcount (covered[vlit (lit)]) < 2) // might not work with other compilers than gcc
      continue;
    candidates.push_back (lit);
  }

  // now only quadratic in the number of candidates.
  // We can ignore the symmetric case as well.
  for (unsigned i = 0; i < candidates.size (); i++) {
    const int lit = candidates[i];
    vector<int> probe_i;
    for (unsigned j = i + 1; j < candidates.size (); j++) {
      const int other = candidates[j];
      vector<int> probe_j;
      assert (lit != other);
      if (lit == -other) continue;
      if (covered[vlit (lit)] ^ covered[vlit (other)] != UINT64_MAX) continue;
      // we have found a set of candidates we we check wether they are golden
      
    }
  }
  
}


void CaDiCaL::Internal::transmute_round (uint64_t propagation_limit) {
  if (unsat)
    return;
  if (terminated_asynchronously ())
    return;
    
  last.transmute.propagations = stats.propagations.search;
  PHASE ("transmute", stats.transmutations,
         "starting transmutation round propagation limit %" PRId64 "", propagation_limit);

  // Fill the schedule. We sort neither the clauses nor the schedule.
  // Previously already transmuted clauses cannot be candidates again.
  //
  Transmuter transmuter ();

  for (const auto &c : clauses) {
    if (!consider_to_transmute_clause (c))
      continue;
    transmuter.schedule.push_back (c);
  }

  shrink_vector (transmuter.schedule);

  // Remember old values of counters to summarize after each round with
  // verbose messages what happened in that round.
  //
  int64_t checked = stats.transmutechecks;
  int64_t units = stats.transmuteunits;
  int64_t hyperbinaries = stats.transmutehb;
  int64_t golden = stats.transmutegold;

  int64_t scheduled = transmuter.schedule.size ();
  stats.transmutesched += scheduled;

  PHASE ("transmute", stats.transmutations,
         "scheduled %" PRId64 " clauses to be transmuted %.0f%%", scheduled,
         percent (scheduled, stats.current.irredundant));

  // Limit the number of propagations during transmutation as in 'probe'.
  //
  const int64_t limit = stats.propagations.transmute + propagation_limit;

  // Transmute all candidates.
  //
  while (!unsat && !terminated_asynchronously () &&
         !transmuter.schedule.empty () && stats.propagations.transmute < limit) {
    Clause *c = transmuter.schedule.back ();
    transmuter.schedule.pop_back ();
    transmute_clause (transmuter, c);
  }

  assert (!level);

  transmuter.erase (); // Reclaim  memory early.

  checked = stats.transmutechecks - checked;
  units = stats.transmuteunits - units;
  hyperbinaries = stats.transmutehb - hyperbinaries;
  golden = stats.transmutegold - golden;

  PHASE ("transmute", stats.transmutations,
         "checked %" PRId64 " clauses %.02f%% of %" PRId64 " scheduled",
         checked, percent (checked, scheduled), scheduled);
  if (units)
    PHASE ("transmute", stats.transmutations,
           "found %" PRId64 " units %.02f%% of %" PRId64 " checked", units,
           percent (units, checked), checked);
  if (hyperbinaries)
    PHASE ("transmute", stats.transmutations,
           "found %" PRId64 " hyper binaries %.02f per %" PRId64 " checked", hyperbinaries,
           relative (hyperbinaries, checked), checked);
  if (golden)
    PHASE ("transmute", stats.transmutations,
           "found %" PRId64 " golden %.02f per %" PRId64 " checked", golden,
           relative (golden, checked), checked);

  last.transmute.propagations = stats.propagations.search;

  stats.transmutechecks += checked;
  stats.transmuteunits += units;
  stats.transmutehb += hyperbinaries;
  stats.transmutegold += golden;

  bool unsuccessful = !(hyperbinaries + golden + units);
  report ('m', unsuccessful); 
}
/*------------------------------------------------------------------------*/

void CaDiCaL::Internal::transmute () {
  if (!opts.transmute)
    return;
  if (unsat)
    return;
  if (terminated_asynchronously ())
    return;

  assert (!level);

  START_SIMPLIFIER (transmute, TRANSMUTE);
  stats.transmutations++;

  // same schedule as for vivification except that there is only one round
  //
  int64_t limit = stats.propagations.search;
  limit -= last.transmute.propagations;
  limit *= 1e-3 * opts.transmutereleff;
  if (limit < opts.transmutemineff)
    limit = opts.transmutemineff;
  if (limit > opts.transmutemaxeff)
    limit = opts.transmutemaxeff;

  PHASE ("transmute", stats.transmutations,
         "transmutation limit of %" PRId64 " propagations", limit);

  transmute_round (limit);

  STOP_SIMPLIFIER (transmute, TRANSMUTE);
}

} // namespace CaDiCaL
