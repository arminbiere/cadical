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

inline void Internal::transmute_assign (int lit, Clause *reason) {
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
  LOG ("transmute decision %d", lit);
  assert (!level);
  assert (propagated == trail.size ());
  level++;
  control.push_back (Level (lit, trail.size ()));
  stats.transmutedecs++;
  transmute_assign (lit, 0);
}

void Internal::transmute_assign_unit (int lit) {
  require_mode (TRANSMUTE);
  assert (!level);
  assert (active (lit));
  stats.transmuteunits++;
  transmute_assign (lit, 0);
}

/*------------------------------------------------------------------------*/


// This is essentially the same as 'propagate' except that we prioritize and
// always propagate binary clauses first (see our CPAIOR'13 paper on tree
// based look ahead), then immediately stop at a conflict and of course use
// 'transmute_assign' instead of 'search_assign'.  The binary propagation part
// is factored out too. Statistics counters are also different.

inline void Internal::transmute_propagate2 () {
  require_mode (TRANSMUTE);
  while (propagated2 != trail.size ()) {
    const int lit = -trail[propagated2++];
    LOG ("transmute propagating %d over binary clauses", -lit);
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
        // transmute_lrat_for_units (w.blit); TODO later
        transmute_assign (w.blit, w.clause);
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
      transmute_propagate2 ();
    else if (propagated != trail.size ()) {
      const int lit = -trail[propagated++];
      LOG ("transmute propagating %d over large clauses", -lit);
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
              transmute_assign (other, w.clause);
            } else {
              assert (lrat_chain.empty ());
              // transmute_lrat_for_units (other);
              transmute_assign_unit (other);
              lrat_chain.clear ();
            }
            transmute_propagate2 ();
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
  stats.propagations.transmute += delta;
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
  if (c->size > opts.transmutesize)
    return false;
  if (c->transmuted)
    return false;
  return true;
}

uint64_t Internal::backward_check (Transmuter &transmuter, int lit) {
  assert (!level);
  assert (!val (lit));

  transmute_assign_decision (-lit);

  // hot spot
  if (!transmute_propagate ()) {
    LOG ("no need for helper clauses because %d unit under rup", lit);
    backtrack (level - 1);
    conflict = 0;
    return UINT64_MAX;
  }
  uint64_t covered = 0;
  int idx = 0;
  for (const auto & other : transmuter.current) {
    idx++;
    const auto &tmp = val (other);
    if (tmp >= 0) continue;
    // we have other -> lit and -lit -> -other by rup
    covered += (uint64_t) 1 << (idx - 1);  // mark other
  }
  backtrack (level - 1);
  return covered;
}

void Internal::learn_helper_binaries (Transmuter &transmuter, int lit, uint64_t forward, uint64_t backward) {
  int idx = 0;
  assert (clause.empty ());
  clause.push_back (lit);
  for (const auto & other : transmuter.current) {
    idx++;
    if (!(forward & (1 << (idx - 1)))) continue;
    if ((backward & (1 << (idx - 1)))) continue;
    // learn binary -lit -> -other
    clause.push_back (-other);
    new_hyper_binary_resolved_clause (true, 2);
    stats.transmutehb++;
    assert (!clause.empty ());
    clause.pop_back ();
  }
  clause.clear ();
}

void Internal::transmute_clause (Transmuter &transmuter, Clause *c) {

  // at least length 4 glue 2 clauses
  assert (c->size > 3);
  assert (c->glue > 1);
  assert (!c->transmuted);

  c->transmuted = true; // remember transmuted clauses

  if (c->garbage)
    return;

  // First check whether the candidate clause is already satisfied and at
  // the same time copy its non fixed literals to 'current'.
  //
  int satisfied = 0;
  auto &current = transmuter.current;
  current.clear ();

  for (const auto &lit : *c) {
    const int tmp = fixed (lit);
    if (tmp > 0) {
      satisfied = lit;
      break;
    } else if (!tmp)
      current.push_back (lit);
  }
  assert (current.size () <= 64);

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
  covered.resize (max_var * 2 + 2);
  // for (unsigned i = 0; i < covered.size (); i++)
  //   covered[i] = 0;

  unsigned idx = 0;
  unsigned size = current.size ();
  const auto end = current.end ();
  auto p = current.begin ();
  auto q = p;

  // Go over the literals in the candidate clause.
  //
  while (q != end) {
    const auto &lit = *p++ = *q++;
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
    
    transmute_assign_decision (lit);

    // hot spot
    if (!transmute_propagate ()) {
      LOG ("learning %d and skipping now falsified %d", -lit, lit);
      backtrack (level - 1);
      conflict = 0;
      assert (!val (lit));
      transmute_assign_unit (-lit);  // might have unwanted side effects later
      p--;
      idx--;
      size--;
      if (!propagate ()) {
        LOG ("propagation after learning unit results in inconsistency");
        learn_empty_clause ();
        return;
      }
      if (size < 4) {
        LOG (c, "too short after unit simplification");
        return;
      }
      c->transmuted = false;                // reschedule c and return
      transmuter.schedule.push_back (c);
      return;
    }
    
    assert  (level == 1);
    if (control[level].trail + 1 == (int) trail.size ()) {
      backtrack (level - 1); // early abort because no propagations
      stats.transmuteabort++;
      return;
    }
    for (size_t begin = control[level].trail + 1; begin < trail.size (); begin++) {
      const auto & other = trail[begin];
      covered[vlit (other)] += (uint64_t) 1 << (idx - 1);  // mark other
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
  
  // check that no lit in current is assigned (might break because of units)
  // TODO: if this breaks need to improve.
  //
#ifndef NDEBUG
  for (const auto & lit : current) assert (!val (lit));
#endif
  
  // now we have to analyze 'covered' in order to find out if there are
  // a pair of literals that covers the clause in the above described way.
  // This is quadratic in the number of literals. To improve performance we
  // filter for candidates which cover at least two literals first.
  //
  vector<int> candidates;
  for (const auto & lit : lits) {
    if (val (lit)) continue;  // do not consider unit assigned literals
    if (__builtin_popcount (covered[vlit (lit)]) < 2) // might not work with other compilers than gcc
      continue;
    candidates.push_back (lit);
  }

  stats.transmutedcandidates += (candidates.size () > 1);
  const uint64_t covering = ((uint64_t) 1 << current.size ()) - 1;
  vector<int> units;
  bool candidate = false;

  // now only quadratic in the number of candidates.
  // We can ignore the symmetric case as well.
  for (unsigned i = 0; i < candidates.size (); i++) {
    const int lit = candidates[i];
    assert (!val (lit));  // TODO: might be a problem if this does not hold
    uint64_t probe_i;
    int probed = 0;
    if (covered[vlit (lit)] == covering) {  // special case of unit
#ifndef NDEBUG  // assert lit not in current
      for (const auto & other : current) assert (other != lit && other != -lit);
#endif
      probe_i = backward_check (transmuter, lit);
      learn_helper_binaries (transmuter, lit, covered[vlit (lit)], probe_i);
      if (probe_i != UINT64_MAX) stats.transmutegoldunits++;
      units.push_back (lit);
      // delete_clause = true;
      continue;
    }
    for (unsigned j = i + 1; j < candidates.size (); j++) {
      const int other = candidates[j];
      assert (!val (other));
      uint64_t probe_j;
      assert (lit != other);
      if (lit == -other) continue;
      assert (covered[vlit (lit)] <= covering);
      if ((covered[vlit (lit)] | covered[vlit (other)]) != covering) continue;
      // we have found a set of candidates we we check wether they are golden
      if (!probed) probe_i = backward_check (transmuter, lit);
      if (probe_i == UINT64_MAX) {   // lit is unit by rup
        units.push_back (lit);
        break;
      }
      probed = 1;
      probe_j = backward_check (transmuter, other); // may be probed again later
      if (probe_j == UINT64_MAX) {   // other is unit by rup
        units.push_back (other);  // in theory these could end up in units multiple times.
        continue;
      }
      //if (__builtin_popcount (probe_j) > current.size ()-2) break;
      //if (__builtin_popcount (probe_i) >  current.size ()-2) continue;
      //if (__builtin_popcount ((probe_j ^ probe_i) & probe_j) < 2) continue;
      //if (__builtin_popcount ((probe_i ^ probe_j) & probe_i) < 2) continue;
      assert (probed);
      if (probed == 1)
        learn_helper_binaries (transmuter, lit, covered[vlit (lit)], probe_i);
      if (!candidate) {
        stats.transmutedclauses++;
        candidate = true;
      }
      probed = 2;
      learn_helper_binaries (transmuter, other, covered[vlit (other)], probe_j);
      assert (clause.empty ());
      clause.push_back (lit);
      clause.push_back (other);
      new_golden_binary ();
      stats.transmutegold++;
      // delete_clause = true;
      clause.clear ();
    }
  }
  for (const auto & lit : units) {
    if (val (lit)) continue;
    transmute_assign_unit (lit);
  }
  if (!units.empty ()) {
    if (!propagate ()) learn_empty_clause ();
  }
  // if (delete_clause && c->redundant) mark_garbage (c);
}


int64_t CaDiCaL::Internal::transmute_round (uint64_t propagation_limit) {
  if (unsat)
    return 0;
  if (terminated_asynchronously ())
    return 0;
    
  PHASE ("transmute", stats.transmutations,
         "starting transmutation round propagation limit %" PRId64 "", propagation_limit);

  // Fill the schedule. We sort neither the clauses nor the schedule.
  // Previously already transmuted clauses cannot be candidates again.
  //
  Transmuter transmuter;

  vector<Clause *> pre_cand;
  for (const auto &c : clauses) {
    if (c->size == 2) {
      noccs (c->literals[0])++;
      noccs (c->literals[1])++;
    }
    if (!consider_to_transmute_clause (c))
      continue;
    pre_cand.push_back (c);
  }

  for (const auto &c : pre_cand) {
    bool cand = true;
    for (int i = 0; i < c->size; i++) {
      if (!noccs (-(c->literals[i]))) {
        cand = false;
        break;
      }
    }
    if (cand)
      transmuter.schedule.push_back (c);
  }
  
  shrink_vector (transmuter.schedule);
  
  stable_sort (transmuter.schedule.rbegin (), transmuter.schedule.rend (), clause_smaller_size ());
  
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
  const int64_t remaining_limit = limit - stats.propagations.transmute;

  bool unsuccessful = !(hyperbinaries + golden + units);
  report ('m', unsuccessful);
  if (remaining_limit < 0) return 0;
  return remaining_limit;
}
/*------------------------------------------------------------------------*/

void CaDiCaL::Internal::transmute () {
  if (lrat) // TODO remove for lrat, for now incompatible
    return;
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

  init_noccs ();

  limit = transmute_round (limit);
  // if (limit) {
  //   transmute_round (limit);
  // }
  reset_noccs ();

  STOP_SIMPLIFIER (transmute, TRANSMUTE);
}

} // namespace CaDiCaL
