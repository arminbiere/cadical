#include "refactor.hpp"
#include "internal.hpp"
#include "util.hpp"
#include <algorithm>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/
// Weird refactoring, targeting factored gates.
// As for refactoring, we have a separate dedicated propagation routine,
// which prefers to propagate binary clauses first.  It also uses its own
// assignment procedure 'refactor_assign', which does not mess with phase
// saving during search nor the conflict and other statistics and further
// can be inlined separately here.

inline void Internal::refactor_assign (int lit, Clause *reason) {
  require_mode (REFACTOR);
  const int idx = vidx (lit);
  assert (!vals[idx]);
  assert (!flags (idx).eliminated () || !reason);
  Var &v = var (idx);
  v.level = level;               // required to reuse decisions
  v.trail = (int) trail.size (); // used in 'refactor_better_watch'
  assert ((int) num_assigned < max_var);
  num_assigned++;
  v.reason = level ? reason : 0; // for conflict analysis
  if (!level)
    learn_unit_clause (lit);
  const signed char tmp = sign (lit);
  vals[idx] = tmp;
  vals[-idx] = -tmp;
  assert (val (lit) > 0);
  assert (val (-lit) < 0);
  trail.push_back (lit);
  LOG (reason, "refactor assign %d", lit);
}

// Assume negated literals in candidate clause.

void Internal::refactor_assume (int lit) {
  require_mode (REFACTOR);
  level++;
  control.push_back (Level (lit, trail.size ()));
  LOG ("refactor decide %d", lit);
  assert (level > 0);
  assert (propagated == trail.size ());
  refactor_assign (lit, 0);
}

// Dedicated routine similar to 'propagate' in 'propagate.cpp' and
// 'probe_propagate' with 'probe_propagate2' in 'probe.cpp'.  Please refer
// to that code for more explanation on how propagation is implemented.

bool Internal::refactor_propagate (int64_t &ticks) {
  require_mode (REFACTOR);
  assert (!unsat);
  START (propagate);
  int64_t before = propagated2 = propagated;
  for (;;) {
    if (propagated2 != trail.size ()) {
      const int lit = -trail[propagated2++];
      LOG ("refactor propagating %d over binary clauses", -lit);
      Watches &ws = watches (lit);
      ticks +=
          1 + cache_lines (ws.size (), sizeof (const_watch_iterator *));
      for (const auto &w : ws) {
        if (!w.binary ())
          continue;
        const signed char b = val (w.blit);
        if (b > 0)
          continue;
        if (b < 0)
          conflict = w.clause; // but continue
        else {
          ticks++;
          build_chain_for_units (w.blit, w.clause, 0);
          refactor_assign (w.blit, w.clause);
          lrat_chain.clear ();
        }
      }
    } else if (!conflict && propagated != trail.size ()) {
      const int lit = -trail[propagated++];
      LOG ("refactor propagating %d over large clauses", -lit);
      Watches &ws = watches (lit);
      const const_watch_iterator eow = ws.end ();
      const_watch_iterator i = ws.begin ();
      ticks += 1 + cache_lines (ws.size (), sizeof (*i));
      watch_iterator j = ws.begin ();
      while (i != eow) {
        const Watch w = *j++ = *i++;
        if (w.binary ())
          continue;
        if (val (w.blit) > 0)
          continue;
        ticks++;
        if (w.clause->garbage) {
          j--;
          continue;
        }
        literal_iterator lits = w.clause->begin ();
        const int other = lits[0] ^ lits[1] ^ lit;
        const signed char u = val (other);
        if (u > 0)
          j[-1].blit = other;
        else {
          const int size = w.clause->size;
          const const_literal_iterator end = lits + size;
          const literal_iterator middle = lits + w.clause->pos;
          literal_iterator k = middle;
          signed char v = -1;
          int r = 0;
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
            j[-1].blit = r;
          else if (!v) {
            LOG (w.clause, "unwatch %d in", r);
            lits[0] = other;
            lits[1] = r;
            *k = lit;
            ticks++;
            watch_literal (r, lit, w.clause);
            j--;
          } else if (!u) {
            ticks++;
            assert (v < 0);
            refactor_chain_for_units (other, w.clause);
            refactor_assign (other, w.clause);
            lrat_chain.clear ();
          } else {
            assert (u < 0);
            assert (v < 0);
            conflict = w.clause;
            break;
          }
        }
      }
      if (j != i) {
        while (i != eow)
          *j++ = *i++;
        ws.resize (j - ws.begin ());
      }
    } else
      break;
  }
  int64_t delta = propagated2 - before;
  stats.propagations.refactor += delta;
  if (conflict)
    LOG (conflict, "conflict");
  STOP (propagate);
  return !conflict;
}

// Common code to actually strengthen a candidate clause.  The resulting
// strengthened clause is communicated through the global 'clause'.

void Internal::refactor_strengthen (Clause *c, int64_t &ticks) {

  assert (!clause.empty ());

  if (clause.size () == 1) {

    backtrack_without_updating_phases ();
    const int unit = clause[0];
    LOG (c, "refactoring shrunken to unit %d", unit);
    assert (!val (unit));
    assign_unit (unit);
    // lrat_chain.clear ();   done in search_assign
    stats.refactorunits++;

    bool ok = refactor_propagate (ticks);
    if (!ok)
      learn_empty_clause ();

  } else {

    // See explanation before 'refactor_better_watch' above.
    //

    int new_level = level;

    const int lit0 = clause[0];
    signed char val0 = val (lit0);
    if (val0 < 0) {
      const int level0 = var (lit0).level;
      LOG ("1st watch %d negative at level %d", lit0, level0);
      new_level = level0 - 1;
    }

    const int lit1 = clause[1];
    const signed char val1 = val (lit1);
    if (val1 < 0 && !(val0 > 0 && var (lit0).level <= var (lit1).level)) {
      const int level1 = var (lit1).level;
      LOG ("2nd watch %d negative at level %d", lit1, level1);
      new_level = level1 - 1;
    }

    assert (new_level >= 0);
    if (new_level < level)
      backtrack (new_level);

    assert (val (lit0) >= 0);
    assert (val (lit1) >= 0 || (val (lit0) > 0 && val (lit1) < 0 &&
                                var (lit0).level <= var (lit1).level));

    Clause *d = new_clause_as (c);
    LOG (c, "before refactoring");
    LOG (d, "after refactoring");
    (void) d;
  }
  clause.clear ();
  mark_garbage (c);
  lrat_chain.clear ();
  ++stats.refactorstrs;
}

/*------------------------------------------------------------------------*/

// Conflict analysis from 'start' which learns a decision only clause.
//
// We cannot use the stack-based implementation of Kissat, because we need
// to iterate over the conflict in topological ordering to produce a valid
// LRAT proof
void Internal::refactor_analyze (Clause *start, bool &subsumes,
                                 Clause **subsuming,
                                 const Clause *const candidate, int implied,
                                 bool &redundant) {
  const auto &t = &trail; // normal trail, so next_trail is wrong
  int i = t->size ();     // Start at end-of-trail.
  Clause *reason = start;
  assert (reason);
  assert (!trail.empty ());
  int uip = trail.back ();
  bool mark_implied = (implied);

  while (i >= 0) {
    if (reason) {
      redundant = (redundant || reason->redundant);
      subsumes = (start != reason && reason->size <= start->size);
      LOG (reason, "resolving on %d with", uip);
      for (auto other : *reason) {
        const Var v = var (other);
        Flags &f = flags (other);
        if (!marked2 (other) && v.level) {
          LOG ("not subsuming due to lit %d", other);
          subsumes = false;
        }
        if (!val (other)) {
          LOG ("skipping unset lit %d", other);
          continue;
        }
        if (other == uip) {
          continue;
        }
        if (!v.level) {
          if (f.seen || !lrat || reason == start)
            continue;
          LOG ("unit reason for %d", other);
          int64_t id = unit_id (-other);
          LOG ("adding unit reason %" PRId64 " for %s", id, LOGLIT (other));
          unit_chain.push_back (id);
          f.seen = true;
          analyzed.push_back (other);
          continue;
        }
        if (mark_implied && other != implied) {
          LOG ("skipping non-implied literal %d on current level", other);
          continue;
        }

        assert (val (other));
        if (f.seen)
          continue;
        LOG ("pushing lit %d", other);
        analyzed.push_back (other);
        f.seen = true;
      }
      if (reason != start && reason->redundant) {
        const int new_glue = recompute_glue (reason);
        promote_clause (reason, new_glue);
      }
      if (subsumes) {
        assert (reason);
        LOG (reason, "clause found subsuming");
        LOG (candidate, "clause found subsumed");
        *subsuming = reason;
        return;
      }
    } else {
      LOG ("refactor analyzed decision %d", uip);
      clause.push_back (-uip);
    }
    mark_implied = false;

    uip = 0;
    while (!uip && i > 0) {
      assert (i > 0);
      const int lit = (*t)[--i];
      if (!var (lit).level)
        continue;
      if (flags (lit).seen)
        uip = lit;
    }
    if (!uip)
      break;
    LOG ("uip is %d", uip);
    Var &w = var (uip);
    reason = w.reason;
    if (lrat && reason)
      lrat_chain.push_back (reason->id);
  }
  (void) candidate;
}

/*------------------------------------------------------------------------*/
// First decide which clause (candidate or conflict) to analyze and
// how to do it. We also prepare the clause by removing units.
void Internal::refactor_deduce (Clause *candidate, Clause *conflict,
                                int implied, Clause **subsuming,
                                bool &redundant) {
  assert (lrat_chain.empty ());
  bool subsumes;
  Clause *reason;

  assert (clause.empty ());
  if (implied) {
    reason = candidate;
    mark2 (candidate);
    const int not_implied = -implied;
    assert (var (not_implied).level);
    Flags &f = flags (not_implied);
    f.seen = true;
    LOG ("pushing implied lit %d", not_implied);
    analyzed.push_back (not_implied);
    clause.push_back (implied);
  } else {
    reason = (conflict ? conflict : candidate);
    assert (reason);
    assert (!reason->garbage || reason->size == 2);
    mark2 (candidate);
    subsumes = (candidate != reason);
    redundant = reason->redundant;
    LOG (reason, "resolving with");
    if (lrat)
      lrat_chain.push_back (reason->id);
    for (auto lit : *reason) {
      const Var &v = var (lit);
      Flags &f = flags (lit);
      assert (val (lit) < 0);
      if (!v.level) {
        if (!lrat)
          continue;
        LOG ("adding unit %d", lit);
        if (!f.seen) {
          // nevertheless we can use var (l) as if l was still assigned
          // because var is updated lazily
          int64_t id = unit_id (-lit);
          LOG ("adding unit reason %" PRId64 " for %s", id, LOGLIT (lit));
          unit_chain.push_back (id);
        }
        f.seen = true;
        analyzed.push_back (lit);
        continue;
      }
      assert (v.level);
      if (!marked2 (lit)) {
        LOG ("lit %d is not marked", lit);
        subsumes = false;
      }
      LOG ("analyzing lit %d", lit);
      LOG ("pushing lit %d", lit);
      analyzed.push_back (lit);
      f.seen = true;
    }
    if (reason != candidate && reason->redundant) {
      const int new_glue = recompute_glue (reason);
      promote_clause (reason, new_glue);
    }
    if (subsumes) {
      assert (candidate != reason);
#ifndef NDEBUG
      int nonfalse_reason = 0;
      for (auto lit : *reason)
        if (!fixed (lit))
          ++nonfalse_reason;

      int nonfalse_candidate = 0;
      for (auto lit : *candidate)
        if (!fixed (lit))
          ++nonfalse_candidate;

      assert (nonfalse_reason <= nonfalse_candidate);
#endif
      LOG (candidate, "refactor subsumed 0");
      LOG (reason, "refactor subsuming 0");
      *subsuming = reason;
      unmark (candidate);
      if (lrat)
        lrat_chain.clear ();
      return;
    }
  }

  refactor_analyze (reason, subsumes, subsuming, candidate, implied,
                    redundant);
  unmark (candidate);
  if (subsumes) {
    assert (*subsuming);
    LOG (candidate, "refactor subsumed");
    LOG (*subsuming, "refactor subsuming");
    if (lrat)
      lrat_chain.clear ();
  }
}

/*------------------------------------------------------------------------*/

// Main function: try to refactor this candidate clause in the given mode.

bool Internal::refactor_clause (Refactoring &refactoring, Clause *c) {

  assert (c->size > 2); // see (NO-BINARY) below
  assert (analyzed.empty ());

  assert (!c->garbage);

  auto &ticks = refactoring.ticks;
  ticks++;

  // First check whether the candidate clause is already satisfied and at
  // the same time copy its non fixed literals to 'sorted'.  The literals
  // in the candidate clause might not be sorted anymore due to replacing
  // watches during propagation, even though we sorted them initially
  // while pushing the clause onto the schedule and sorting the schedule.
  //

  for (const auto &lit : *c) {
    const int tmp = fixed (lit);
    if (tmp > 0) {
      LOG (c, "satisfied by propagated unit %d", lit);
      mark_garbage (c);
      return false;
    }
  }

  // The actual refactoring checking is performed here, by assuming the
  // negation of each of the remaining literals of the clause in turn and
  // propagating it.  If a conflict occurs or another literal in the
  // clause becomes assigned during propagation, we can stop.
  //
  LOG (c, "refactoring checking");
  stats.refactorchecks++;

  // If the decision 'level' is non-zero, then we can reuse decisions for
  // the previous candidate, and avoid re-propagating them.  In preliminary
  // experiments this saved between 30%-50% decisions (and thus
  // propagations), which in turn lets us also refactor more clauses within
  // the same propagation bounds, or terminate earlier if refactor runs to
  // completion.
  // TODO: do this eagerly just for the two gate literals in the clause
  // (which are assigned first anyway).
  //
  if (level) {

    backtrack_without_updating_phases (0);

    // As long the (remaining) literals of the sorted clause match
    // decisions on the trail we just reuse them.
    //

    LOG ("reused %d decision levels from %d", level, orig_level);
  }

  LOG (sorted, "sorted size %zd probing schedule", sorted.size ());

  int subsume = 0; // determined to be redundant / subsumed

  // If the candidate is redundant, i.e., we are in redundant mode, the
  // clause is subsumed (in one of the two cases below where 'subsume' is
  // assigned) and further all reasons involved are only binary clauses,
  // then this redundant clause is what we once called a hidden tautology,
  // and even for redundant clauses it makes sense to remove the candidate.
  // It does not add anything to propagation power of the formula.  This is
  // the same argument as removing transitive clauses in the binary
  // implication graph during transitive reduction.
  //

  // Go over the literals in the candidate clause in sorted order.
  // TODO: prioritize the gate literals first.
  //
  for (const auto &lit : clause) {

    // Exit loop as soon a literal is positively implied (case '@5' below)
    // or propagation of the negation of a literal fails ('@6').
    //
    if (subsume)
      break;

    // We keep on assigning literals, even though we know already that we
    // can remove one (was negatively implied), since we either might run
    // into the 'subsume' case above or more false literals become implied.
    // In any case this might result in stronger vivified clauses.  As a
    // consequence continue with this loop even if 'remove' is non-zero.

    const signed char tmp = val (lit);

    if (tmp) { // literal already assigned

      const Var &v = var (lit);
      assert (v.level);
      if (!v.reason) {
        LOG ("skipping decision %d", lit);
        continue;
      }

      if (tmp < 0) {
        assert (v.level);
        LOG ("literal %d is already false and can be removed", lit);
        continue;
      }

      assert (tmp > 0);
      LOG ("subsumed since literal %d already true", lit);
      subsume = lit; // will be able to subsume candidate '@5'
      break;
    }

    assert (!tmp);

    stats.refactordecs++;
    refactor_assume (-lit);
    LOG ("negated decision %d score %" PRIu64 "", lit, noccs (lit));

    if (!refactor_propagate (ticks)) {
      break; // hot-spot
    }
  }

  Clause *subsuming = nullptr;
  bool redundant = false;
  refactor_deduce (c, conflict, subsume, &subsuming, redundant);

  bool res;

  // reverse lrat_chain. We could probably work with reversed iterators
  // (views) to be more efficient but we would have to distinguish in proof
  //
  if (lrat) {
    for (auto id : unit_chain)
      lrat_chain.push_back (id);
    unit_chain.clear ();
    reverse (lrat_chain.begin (), lrat_chain.end ());
  }

  // TODO: learn clause to shorten c.
  if (!subsume && !conflict) {
    LOG (c,
         "refactoring unsuccessful (no conflict and no subsumed literal)");
  } else {
    LOG (c, "refactoring successful");
  }

  if (conflict) {
    LOG ("forcing backtracking at least one level after conflict");
    backtrack_without_updating_phases (level - 1);
  }

  clause.clear ();
  clear_analyzed_literals (); // TODO why needed?
  lrat_chain.clear ();
  conflict = nullptr;

  return res;
}

// when we can strengthen clause c we have to build lrat.
// uses f.seen so do not forget to clear flags afterwards.
// this can happen in three cases. (1), (2) are only sound in redundant mode
// (1) literal l in c is positively implied. in this case we call the
// function with (l, l.reason). This justifies the reduction because the new
// clause c' will include l and all decisions so l.reason is a conflict
// assuming -c' (2) conflict during refactor propagation. function is called
// with (0, conflict) similar to (1) but more direct. (3) some literals in c
// are negatively implied and can therefore be removed. in this case we call
// the function with (0, c). originally we justified each literal in c on
// its own but this is not actually necessary.
//

// Non-recursive version, as some bugs have been found by Dominik Schreiber
// during his very large experiments. DFS over the reasons with preordering
// (aka we explore the entire reason before exploring deeper)
void Internal::refactor_build_lrat (
    int lit, Clause *reason,
    std::vector<std::tuple<int, Clause *, bool>> &stack) {
  assert (stack.empty ());
  stack.push_back ({lit, reason, false});
  while (!stack.empty ()) {
    int lit;
    Clause *reason;
    bool finished;
    std::tie (lit, reason, finished) = stack.back ();
    LOG ("refactor LRAT justifying %d", lit);
    stack.pop_back ();
    if (lit && flags (lit).seen) {
      LOG ("skipping already justified");
      continue;
    }
    if (finished) {
      lrat_chain.push_back (reason->id);
      if (lit && reason) {
        Flags &f = flags (lit);
        f.seen = true;
        analyzed.push_back (lit); // assert (val (other) < 0);
        assert (flags (lit).seen);
      }
      continue;
    } else
      stack.push_back ({lit, reason, true});
    for (const auto &other : *reason) {
      if (other == lit)
        continue;
      Var &v = var (other);
      Flags &f = flags (other);
      if (f.seen)
        continue;
      if (!v.level) {
        const int64_t id = unit_id (-other);
        lrat_chain.push_back (id);
        f.seen = true;
        analyzed.push_back (other);
        continue;
      }
      if (v.reason) { // recursive justification
        LOG ("refactor LRAT pushing %d", other);
        stack.push_back ({other, v.reason, false});
      }
    }
  }
  stack.clear ();
}

// calculate lrat_chain
//
inline void Internal::refactor_chain_for_units (int lit, Clause *reason) {
  if (!lrat)
    return;
  if (level)
    return; // not decision level 0
  assert (lrat_chain.empty ());
  for (auto &reason_lit : *reason) {
    if (lit == reason_lit)
      continue;
    assert (val (reason_lit));
    const int signed_reason_lit = val (reason_lit) * reason_lit;
    int64_t id = unit_id (signed_reason_lit);
    lrat_chain.push_back (id);
  }
  lrat_chain.push_back (reason->id);
}

void Internal::refactor_initialize (Refactoring &refactoring,
                                    int64_t &ticks) {

  for (auto &fg : factored_gates) {
    int found_all_gate_clauses = 0;
    mark (fg.definition), mark (fg.condition), mark (fg.true_branch),
        mark (fg.false_branch);
    refactoring.gate_clauses.emplace_back ();
    refactoring.gate_clauses.back ().first = fg.definition;
    for (const auto &c : clauses) {
      ++ticks;
      if (!c->redundant && c->size == 3) {
        bool gate = true;
        for (auto &lit : *c) {
          if (!marked (lit) && !marked (!lit)) {
            gate = false;
            break;
          }
        }
        if (!gate)
          continue;
        found_all_gate_clauses++;
        refactoring.gate_clauses.back ().second.push_back (c);
      }
      if (!c->redundant)
        continue; // see also (NO-BINARY) above
      if (c->size == 2)
        continue; // see also (NO-BINARY) above
      ++ticks;
      size_t found_true = 0;
      size_t found_false = 0;
      bool skip = false;
      for (auto &lit : *c) {
        if (lit == fg.definition) {
          skip = true;
          break;
        }
        if (lit == fg.condition)
          found_true++;
        if (lit == -fg.condition)
          found_false++;
        if (lit == fg.true_branch)
          found_true++;
        if (lit == -fg.true_branch)
          found_true++;
        if (lit == fg.false_branch)
          found_false++;
        if (lit == -fg.false_branch)
          found_false++;
      }
      if (skip)
        continue;
      if (found_true == 2 || found_false == 2) {
        refactoring.candidates.emplace_back ();
        refactoring.candidates.back ().second = c;
        refactoring.candidates.back ().first = fg.definition;
      }
    }
    unmark (fg.definition), unmark (fg.condition), unmark (fg.true_branch),
        unmark (fg.false_branch);
  }

  refactor_propagate (ticks);

  PHASE ("refactor", stats.refactor, "init");
}

void Internal::refactor_round (Refactoring &refactoring,
                               int64_t ticks_limit) {

  if (unsat)
    return;
  if (terminated_asynchronously ())
    return;

  PHASE ("refactor", stats.refactor,
         "starting refactoring round ticks limit %" PRId64
         " with %zu clauses",
         ticks_limit, refactoring.candidates.size ());

  assert (watching ());

  int64_t ticks = 0;

  // Remember old values of counters to summarize after each round with
  // verbose messages what happened in that round.
  //
  int64_t checked = stats.refactorchecks;
  int64_t strengthened = stats.refactorstrs;
  int64_t units = stats.refactorunits;

  int64_t scheduled = refactoring.candidates.size ();
  stats.refactorsched += scheduled;

  PHASE ("refactor", stats.refactor,
         "scheduled %" PRId64 " clauses to be vivified %.0f%%", scheduled,
         percent (scheduled, stats.current.irredundant));

  // Limit the number of propagations during refactoring as in 'probe'.
  //
  const int64_t limit = ticks_limit - stats.ticks.refactor;
  assert (limit >= 0);

  // the clauses might still contain set literals, so propagation since the
  // beginning
  propagated2 = propagated = 0;

  if (!unsat && !propagate ()) {
    LOG ("propagation after connecting watches in inconsistency");
    learn_empty_clause ();
  }

  auto &schedule = refactoring.candidates;
  refactoring.ticks = ticks;
  while (!unsat && !terminated_asynchronously () && !schedule.empty () &&
         refactoring.ticks < limit) {
    Clause *c = schedule.back ().second; // Next candidate.
    schedule.pop_back ();
    refactor_clause (refactoring, c);
  }

  if (level)
    backtrack_without_updating_phases ();

  if (!unsat) {

    // Since redundant clause were disconnected during propagating vivified
    // units in redundant mode, and further irredundant clauses are
    // arbitrarily sorted, we have to propagate all literals again after
    // connecting the first two literals in the clauses, in order to
    // reestablish the watching invariant.
    //
    propagated2 = propagated = 0;

    if (!propagate ()) {
      LOG ("propagating refactored units leads to conflict");
      learn_empty_clause ();
    }
  }

  checked = stats.refactorchecks - checked;
  strengthened = stats.refactorstrs - strengthened;
  units = stats.refactorunits - units;

  PHASE ("refactor", stats.refactor,
         "checked %" PRId64 " clauses %.02f%% of %" PRId64
         " scheduled using %" PRIu64 " ticks",
         checked, percent (checked, scheduled), scheduled,
         refactoring.ticks);
  if (units)
    PHASE ("refactor", stats.refactor,
           "found %" PRId64 " units %.02f%% of %" PRId64 " checked", units,
           percent (units, checked), checked);
  if (strengthened)
    PHASE ("refactor", stats.refactor,
           "strengthened %" PRId64 " clauses %.02f%% of %" PRId64
           " checked",
           strengthened, percent (strengthened, checked), checked);

  stats.ticks.refactor += refactoring.ticks;

  bool unsuccessful = !(strengthened + units);
  report ('y', unsuccessful);
}

/*------------------------------------------------------------------------*/

bool Internal::refactor () {

  if (unsat)
    return false;
  if (terminated_asynchronously ())
    return false;
  if (!opts.refactor)
    return false;
  if (!stats.current.irredundant)
    return false;
  if (level)
    backtrack ();
  assert (opts.refactor);
  assert (!level);

  SET_EFFORT_LIMIT (totallimit, refactor, true);

  private_steps = true;

  START_SIMPLIFIER (refactor, REFACTOR);
  stats.refactor++;

  // the effort is normalized by dividing by sumeffort below, hence no need
  // to multiply by 1e-3 (also making the precision better)
  int64_t total = totallimit - stats.ticks.refactor;

  PHASE ("refactor", stats.refactor,
         "refactoring limit of %" PRId64 " ticks", total);
  Refactoring refactoring;

  int64_t init_ticks = 0;

  refactor_initialize (refactoring, init_ticks);
  stats.ticks.refactor += init_ticks;
  int64_t limit = stats.ticks.refactor;
  if (limit > stats.ticks.refactor) {
    assert (limit >= 0);
    refactor_round (refactoring, limit);
  } else {
    LOG ("building the schedule already used our entire ticks budget for "
         "refactor");
  }

  STOP_SIMPLIFIER (refactor, REFACTOR);

  private_steps = false;

  return true;
}

} // namespace CaDiCaL
