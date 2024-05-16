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


bool Internal::backward_check (Transmuter &transmuter, int lit, uint64_t forward) {
  assert (!level);
  assert (!val (lit));

  transmute_assign_decision (-lit);

  // hot spot
  if (!transmute_propagate ()) {
    LOG ("no need for helper clauses because %d unit under rup", lit);
    backtrack (level - 1);
    conflict = 0;
    return false;
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
  if (learn_helper_binaries (transmuter, lit, forward, covered)) {
    if (!transmute_propagate ()) {
      backtrack (level - 1);
      conflict = 0;
      return false;
    }
  }
  return true;
}

bool Internal::learn_helper_binaries (Transmuter &transmuter, int lit, uint64_t forward, uint64_t backward) {
  if (opts.transmutefake) return false;
  int idx = 0;
  bool repropagate = false;
  assert (clause.empty ());
  clause.push_back (lit);
  assert (val (lit) < 0);
  for (const auto & other : transmuter.current) {
    idx++;
    if (other == lit) continue;
    if (!(forward & (1 << (idx - 1)))) continue;
    if ((backward & (1 << (idx - 1)))) continue;
    LOG ("learning helper binary %d %d", lit, -other);
    // learn binary -lit -> -other
    clause.push_back (-other);
    Clause *res = new_hyper_binary_resolved_clause (true, 2);
    transmute_assign (-other, res);
    repropagate = true;
    stats.transmutehb++;
    assert (!clause.empty ());
    clause.pop_back ();
  }
  clause.clear ();
  return repropagate;
}

Clause *Internal::transmute_instantiate_clause (Clause *c, int lit, int other) {
  stats.transmuteinstantiate++;
  clause.push_back (-lit);
  clause.push_back (other);
  Clause *tmp = new_hyper_binary_resolved_clause (true, 2);
  clause.clear ();
  for (const auto &literal : *c) {
    if (literal == lit) continue;
    clause.push_back (literal);
  }
  assert (c->size == (int) clause.size () + 1);
  Clause *d = new_clause_as (c);
  d->transmuted = true;
  clause.clear ();
  mark_garbage (c);
  mark_garbage (tmp);
  return d;
}

void Internal::transmute_clause (Transmuter &transmuter, Clause *c, int64_t limit) {

  // at least length 4 glue 2 clauses
  assert (c->size > 3);
  // assert (c->glue > 1);
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
  // the clause either implies l or k @1. (i.e. c->(l or k) which means we
  // are allowed to learn the clause (l or k))
  // Furthermore, we only consider golden pairs, i.e.,
  // neither -l nor -k imply more than n-2 literals in a clause of size n. @2
  // Thus the smalles candidate size for transmutation is 4.
  // @2 is subsumed by checking that -k -> l.
  // Consider x y u v, with x,y->l and u,v->k. If -l -> (-x and -y and -u),
  // then -l -> v. By transitivity we get -l -> k which would fail our check.
  // We do instantiation on the fly: When we probe a literal a of the clause c
  // and it implies c\{a} then we can learn c\{a} @3
  // Early abort happens when the clause becomes too short @4,
  // either because of probing units or through @3
  // or if a literal does not propagate at all @5. However, @5 can only happen
  // if a unit was learned in a previous iteration of transmute_clause.
  
  LOG (c, "transmutation checking");
  stats.transmutechecks++;

  assert (!level);

  // we use vlit for indexing the covered array.
  vector<uint64_t> covered;
  covered.resize (max_var * 2 + 2);

  unsigned idx = 0;
  unsigned size = current.size ();
  const auto end = current.end ();
  auto p = current.begin ();
  auto q = p;

  // Go over the literals in the candidate clause.
  //
  while (q != end) {
    if (stats.propagations.transmute >= limit) {
      stats.transmuteabort++;
      stats.transmuteabortlimit++;
      c->transmuted = false;                // reschedule c and return
      stats.transmuterescheduled++;
      return;
    }
    const auto &lit = *p++ = *q++;
    idx++;
    assert (!conflict);
    if (val (lit) > 0) {
      LOG (c, "satisfied by propagated unit %d", lit);
      mark_garbage (c);
      stats.transmuteabort++;
      return;
    } else if (val (lit) < 0) {
      LOG ("skipping falsified literal %d", lit);
      p--;
      idx--;
      size--;
      if (size < 4) {
        LOG (c, "too short after unit simplification");  // @4
        stats.transmuteabort++;
        stats.transmuteabortshort++;
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
        LOG (c, "too short after unit simplification");   // @4
        stats.transmuteabort++;
        stats.transmuteabortshort++;
        return;
      }
      c->transmuted = false;                // reschedule c and return
      stats.transmuteabort++;
      stats.transmuterescheduled++;
      transmuter.schedule.push_back (pair<Clause*,int> (c, c->size-1));
      return;
    }
    if (opts.transmuteinst) {
      for (const auto &other : *c) {
        if (other == lit) continue;
        if (val (other) > 0) {
          assert (var (other).level == 1);
          p--;
          idx--;
          size--;
          backtrack (level - 1);
          c = transmute_instantiate_clause (c, lit, other);  // @3
          if (size < 4) {
            LOG (c, "too short after unit simplification");  // @4
            stats.transmuteabort++;
            stats.transmuteabortshort++;
            return;
          }
          break;
        }
      }
      if (!level)
        continue;
    }
    assert  (level == 1);
    if (control[level].trail + 1 == (int) trail.size ()) {
      backtrack (level - 1); // early abort because no propagations @5
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
  
  // check that no lit in current is assigned
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

  stats.transmutedcandidates += (candidates.size ());
  const uint64_t covering = ((uint64_t) 1 << current.size ()) - 1;
  vector<int> units;
  vector<bool> backward_check_performed;
  backward_check_performed.resize (candidates.size ());
  // contains indices for golden binaries
  vector<pair<unsigned, unsigned>> golden_binaries;

  
  // now only quadratic in the number of candidates.
  // We can ignore the symmetric case as well.
  for (unsigned i = 0; i < candidates.size (); i++) {
    const int lit = candidates[i];
    if (level) backtrack ();
    if (stats.propagations.transmute >= limit) {
      stats.transmuteabort++;
      stats.transmuteabortlimit++;
      c->transmuted = false;                // reschedule c and return
      stats.transmuterescheduled++;
      if (golden_binaries.empty () && units.empty ())
        return;
      break;
    }
    assert (!val (lit));  // might be a problem if this does not hold
    if (covered[vlit (lit)] == covering) {  // special case of unit also implies @3
#ifndef NDEBUG  // assert lit not in current
      for (const auto & other : current) assert (other != lit && other != -lit);
#endif
      assert (!backward_check_performed[i]);
      assert (!level);
      backward_check_performed[i] = true;
      backward_check (transmuter, lit, covered[vlit (lit)]);
      units.push_back (lit);
      continue;
    }
    for (unsigned j = i + 1; j < candidates.size (); j++) {
      const int other = candidates[j];
      if (val (other) > 0) continue;
      assert (lit != other);
      if (lit == -other) continue;
      assert (covered[vlit (lit)] <= covering);
      if ((covered[vlit (lit)] | covered[vlit (other)]) != covering) continue;
      if (!backward_check_performed[i]) {
        assert (!level);
        if (stats.propagations.transmute >= limit) {
          stats.transmuteabort++;
          stats.transmuteabortlimit++;
          c->transmuted = false;                // reschedule c and return
          stats.transmuterescheduled++;
          if (golden_binaries.empty () && units.empty ())
            return;
          break;
        }
        backward_check_performed[i] = true;
        if (!backward_check (transmuter, lit, covered[vlit (lit)])) {
          units.push_back (lit);
          break;
        }
      }
      // we can avoid probing lit multiple times by not backtracking so we
      // should be at level 1 here.
      assert (level);
      assert (val (lit) < 0);

      // improved check for -lit -> other (see discussion @2)
      if (val (other) > 0) continue;
      else if (val (other) < 0) {
        units.push_back (lit);  // edge case val (other) < 0 -> learn unit clause
      }
      golden_binaries.push_back (pair<unsigned, unsigned> (i, j));
    }
  }
  if (level) backtrack ();
  if (opts.transmutefake) return;
  if (golden_binaries.size ()) {
    stats.transmutedclauses++;
    if (c->redundant) {
      assert (c->glue - 1 < 64);
      stats.transmutedglue[c->glue - 1]++;
    }
    stats.transmutedsize[current.size ()]++;
  }
  for (const auto & bin : golden_binaries) {
    assert (clause.empty ());
    const unsigned i = bin.first;
    const unsigned j = bin.second;
    const int lit = candidates[i];
    const int other = candidates[j];
    assert (backward_check_performed[i]);
    assert (!level);
    assert (!val (lit) && !val (other));
    // necessary to get rup proofs. Even though we get additional propagations
    // here we do not abort!
    if (!backward_check_performed[j]) {
      backward_check_performed[j] = true;
      if (!backward_check (transmuter, other, covered[vlit (other)])) {
        assert (!level);
        units.push_back (other);
        continue;
      }
      backtrack ();
    }
    if (val (lit) > 0 || val (other) > 0) continue;
    clause.push_back (lit);
    clause.push_back (other);
    new_golden_binary ();
    stats.transmutegold++;
    clause.clear ();
  }
  for (const auto & lit : units) {
    if (val (lit) > 0) continue;
    else if (val (lit) < 0) { // conflict!
      assert (false);
      learn_empty_clause ();
      return;
    }
    transmute_assign_unit (lit);
  }

  if (!units.empty ()) {
    if (!propagate ()) learn_empty_clause ();
  }
  assert (!level);
}


struct transmute_sort_clause {

  bool operator() (pair<Clause*, int> p, pair<Clause*, int> q) const {
    const auto & c = p.first;
    const auto & d = q.first;
    const auto & c_size = p.second;
    const auto & d_size = q.second;
    if (c_size < d_size) return false;
    if (d_size < c_size) return true;
    return c->glue > d->glue;
  }
};


// We consider all clauses of size >= 4 and glue >= 1 for transmutation.
// Clauses bigger 64 are skipped in order to efficiently calculate set cover.
// However, we count non-falsified literals and do not take c->size
// clauses can only be candidates once.
//
void Internal::fill_transmute_schedule (Transmuter &transmuter, bool redundant) {
  vector<Clause *> pre_cand;
  // fill noccs and pre-select candidates with the above criteria
  for (const auto &c : clauses) {
    if (c->garbage) continue;
    bool sat = false;
    int count = 0;
    unsigned first = 0;
    unsigned second = 0;
    // fill noccs to filter for literals which do not propagate at all
    for (const auto &lit : *c) {
      if (val (lit) > 0) { sat = true; break; }
      else if (val (lit) < 0) continue;
      else if (!first) first = lit;
      else if (!second) second = lit;
      count++;
      if (count > 2) break;
    }
    if (sat) continue;
    assert (count > 1);
    if (count == 2) {
      noccs (first)++;
      noccs (second)++;
    }
    if (c->size < 4) continue;
    if (c->redundant != redundant) continue;
    // TODO: test
    // if (redundant && !likely_to_be_kept_clause (c)) continue;
    if (c->transmuted) continue;
    pre_cand.push_back (c);
  }

  for (const auto &c : pre_cand) {
    int count = 0;
    bool cand = true;
    for (int i = 0; i < c->size; i++) {
      if (val (c->literals[i])) continue;
      count++;
      if (count > opts.transmutesize) {
        cand = false;
        break;
      }
      if (!noccs (-(c->literals[i]))) {
        cand = false;
        break;
      }
    }
    if (cand && count > 3)
      transmuter.schedule.push_back (pair<Clause*,int> (c, count));
  }
  
  shrink_vector (transmuter.schedule);
  
  stable_sort (transmuter.schedule.begin (), transmuter.schedule.end (), transmute_sort_clause ());
}


void CaDiCaL::Internal::transmute_round (uint64_t propagation_limit, bool redundant) {
  if (unsat)
    return;
  if (terminated_asynchronously ())
    return;

  PHASE ("transmute", stats.transmutations,
         "starting transmutation round propagation limit %" PRId64 "", propagation_limit);

  // Fill the schedule. We sort neither the clauses nor the schedule.
  // Previously already transmuted clauses cannot be candidates again.
  //
  Transmuter transmuter;

  fill_transmute_schedule (transmuter, redundant);
  
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
    Clause *c = transmuter.schedule.back ().first;
    transmuter.schedule.pop_back ();
    transmute_clause (transmuter, c, limit);
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

  bool unsuccessful = !(hyperbinaries + golden + units);
  report ('m', !opts.reportall && unsuccessful);
  return;
}
/*------------------------------------------------------------------------*/

bool CaDiCaL::Internal::transmute () {
  assert (!lrat); // for fuzzing
  if (lrat) // TODO remove for lrat, for now incompatible
    return false;
  if (!opts.transmute)
    return false;
  if (unsat)
    return false;
  if (terminated_asynchronously ())
    return false;

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

  int64_t hyperbinaries = stats.transmutehb;
  int64_t golden = stats.transmutegold;

  transmute_round (limit, false);
  limit *= 1e-3 * opts.transmuteredeff;
  transmute_round (limit, true);

  reset_noccs ();

  STOP_SIMPLIFIER (transmute, TRANSMUTE);
  return golden != stats.transmutegold || hyperbinaries != stats.transmutehb;
}

} // namespace CaDiCaL
