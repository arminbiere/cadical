#include "refactor.hpp"
#include "internal.hpp"
#include "util.hpp"

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
void Internal::refactor_analyze (Clause *start) {
  const auto &t = &trail; // normal trail, so next_trail is wrong
  int i = t->size ();     // Start at end-of-trail.
  Clause *reason = start;
  assert (reason);
  assert (!trail.empty ());
  int uip = trail.back ();

  while (i >= 0) {
    if (reason) {
      LOG (reason, "resolving on %d with", uip);
      for (auto other : *reason) {
        if (other == uip)
          continue;
        const Var v = var (other);
        Flags &f = flags (other);
        assert (val (other));
        if (f.seen)
          continue;
        if (!v.level) {
          if (f.seen || !lrat)
            continue;
          LOG ("unit reason for %d", other);
          int64_t id = unit_id (-other);
          LOG ("adding unit reason %" PRId64 " for %s", id, LOGLIT (other));
          unit_chain.push_back (id);
          f.seen = true;
          analyzed.push_back (other);
          continue;
        }
        LOG ("pushing lit %d", other);
        analyzed.push_back (other);
        f.seen = true;
      }
    } else {
      LOG ("refactor analyzed decision %d", uip);
      clause.push_back (-uip);
    }

    uip = 0;
    while (!uip && i > 0) {
      assert (i > 0);
      const int lit = (*t)[--i];
      if (!var (lit).level)
        break;
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
}

void Internal::refactor_shrink_candidate (refactor_candidate cand,
                                          refactor_gate fate) {
  const int definition = cand.negdef ? -fate.definition : fate.definition;
  const int cand_branch =
      cand.negcon ? fate.true_branch : fate.false_branch;
  const int other_branch =
      !cand.negcon ? fate.true_branch : fate.false_branch;
  const int condition = cand.negcon ? -fate.condition : fate.condition;
  const int64_t tmp_id_1 = ++clause_id;
  Clause *gate_1 = 0;
  Clause *gate_2 = 0;
  std::vector<int> tmp_clause_1;
  tmp_clause_1.swap (clause);
  clause.clear ();
  const int64_t tmp_id_2 = ++clause_id;
  std::vector<int> tmp_clause_2;
  const int64_t tmp_id_3 = ++clause_id;
  std::vector<int> tmp_clause_3;
  if (proof) {
    // take the two gate clauses that are needed (fate is not ordered)
    for (auto c : fate.clauses) {
      bool g1 = true;
      bool g2 = true;
      for (auto &lit : *c) {
        if (lit == -definition) {
          g1 = false;
          g2 = false;
        } else if (lit == cand_branch) {
          g1 = false;
        } else if (lit == other_branch) {
          g2 = false;
        }
      }
      if (g1)
        gate_1 = c;
      else if (g2)
        gate_2 = c;
    }
    assert (gate_1 && gate_2);

    proof->add_derived_clause (tmp_id_1, true, tmp_clause_1, lrat_chain);
    lrat_chain.clear ();
    clause.clear ();
    tmp_clause_2.push_back (definition);
    for (const auto &lit : tmp_clause_1) {
      if (abs (lit) == abs (other_branch))
        continue;
      tmp_clause_2.push_back (lit);
    }
    if (lrat) {
      lrat_chain.push_back (tmp_id_1);
      lrat_chain.push_back (gate_1->id);
    }
    proof->add_derived_clause (tmp_id_2, true, tmp_clause_2, lrat_chain);
    lrat_chain.clear ();
    proof->delete_clause (tmp_id_1, true, tmp_clause_1);

    tmp_clause_3.push_back (definition);
    for (const auto &lit : *cand.candidate) {
      if (abs (lit) == abs (cand_branch))
        continue;
      tmp_clause_3.push_back (lit);
    }
    if (lrat) {
      lrat_chain.push_back (cand.candidate->id);
      lrat_chain.push_back (gate_2->id);
    }
    proof->add_derived_clause (tmp_id_3, true, tmp_clause_3, lrat_chain);
    lrat_chain.clear ();
    if (lrat) {
      lrat_chain.push_back (tmp_id_2);
      lrat_chain.push_back (tmp_id_3);
    }
  }
  for (const auto &lit : *cand.candidate) {
    if (abs (lit) == abs (condition))
      continue;
    if (abs (lit) == abs (cand_branch))
      clause.push_back (lit);
  }
  new_clause_as (cand.candidate);
  clause.clear ();
  lrat_chain.clear ();
  if (proof) {
    proof->delete_clause (tmp_id_2, true, tmp_clause_2);
    proof->delete_clause (tmp_id_3, true, tmp_clause_3);
  }
}

/*------------------------------------------------------------------------*/

// Main function: try to refactor this candidate clause in the given mode.

bool Internal::refactor_clause (Refactoring &refactoring,
                                refactor_candidate cand) {

  refactor_gate fate = refactoring.gate_clauses[cand.index];
  if (fate.skip)
    return false;

  Clause *c = cand.candidate;
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
    int bt_level = 0;
    if (cand.negcon) {
      if (control[0].decision == fate.condition)
        bt_level = 1;
      if (cand.negdef) {
        if (bt_level && level > 1 &&
            control[1].decision == fate.true_branch)
          bt_level = 2;
      } else {
        if (bt_level && level > 1 &&
            control[1].decision == -fate.true_branch)
          bt_level = 2;
      }
    } else {
      if (control[0].decision == -fate.condition)
        bt_level = 1;
      if (cand.negdef) {
        if (bt_level && level > 1 &&
            control[1].decision == fate.false_branch)
          bt_level = 2;
      } else {
        if (bt_level && level > 1 &&
            control[1].decision == -fate.false_branch)
          bt_level = 2;
      }
    }

    backtrack_without_updating_phases (bt_level);

    // As long the (remaining) literals of the sorted clause match
    // decisions on the trail we just reuse them.
    //

    LOG ("reused %d decision levels", level);
  }

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

  if (!level) {
    int lit = fate.condition;
    if (!cand.negcon)
      lit = -lit;
    const signed char tmp = val (lit);
    if (tmp) {
      LOG ("condition %d is root-level assigned", lit);
      return false;
    }
    stats.refactordecs++;
    refactor_assume (-lit);
    LOG ("condition decision %d", lit);
    if (!refactor_propagate (ticks)) {
      // TODO: conflict analysis
      return false;
    }
  }
  if (level != 1) {
    int lit = -fate.false_branch;
    if (cand.negdef)
      lit = -fate.true_branch;
    const signed char tmp = val (lit);
    if (tmp) {
      LOG ("branch %d is implied by condition (or root-level)", lit);
      return false;
    }
    stats.refactordecs++;
    refactor_assume (-lit);
    LOG ("branch decision %d", lit);
    if (!refactor_propagate (ticks)) {
      // TODO: conflict analysis
      return false;
    }
  }

  // Go over the literals in the candidate clause.
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
      } else if (abs (lit) == abs (fate.true_branch) ||
                 abs (lit) == abs (fate.false_branch))
        continue;

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
    LOG ("negated decision %d", lit);

    if (!refactor_propagate (ticks)) {
      break; // hot-spot
    }
  }

  Clause *reason = conflict;
  if (subsume)
    reason = var (subsume).reason;
  if (!reason)
    return false;

  // fills clause stack and lrat_chain (if applicable).
  refactor_analyze (reason);

  // TODO: learn temporary clauses and use gate clauses to shrink candidate
  refactor_shrink_candidate (cand, fate);

  if (conflict) {
    LOG ("forcing backtracking at least one level after conflict");
    backtrack_without_updating_phases (level - 1);
  }

  clause.clear ();
  clear_analyzed_literals (); // TODO why needed?
  lrat_chain.clear ();
  conflict = nullptr;

  return true;
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

  size_t index = 0;
  for (auto &fg : factored_gates) {
    int found_all_gate_clauses = 0;
    mark2 (fg.definition), mark2 (fg.condition), mark2 (fg.true_branch),
        mark2 (fg.false_branch);
    refactoring.gate_clauses.emplace_back ();
    refactoring.gate_clauses.back ().definition = fg.definition;
    refactoring.gate_clauses.back ().condition = fg.condition;
    refactoring.gate_clauses.back ().true_branch = fg.true_branch;
    refactoring.gate_clauses.back ().false_branch = fg.false_branch;
    refactoring.gate_clauses.back ().skip = false;
    for (const auto &c : clauses) {
      ++ticks;
      if (!c->redundant && c->size == 3) {
        bool gate = true;
        for (auto &lit : *c) {
          if (!marked2 (lit) && !marked2 (-lit)) {
            gate = false;
            break;
          }
        }
        if (!gate)
          continue;
        // TODO: what if the phases do not match
        // or we have duplicated clauses...
        found_all_gate_clauses++;
        refactoring.gate_clauses.back ().clauses.push_back (c);
      }
      if (!c->redundant)
        continue; // see also (NO-BINARY) above
      if (c->size == 2)
        continue; // see also (NO-BINARY) above
      ++ticks;
      size_t found_true = 0;
      size_t found_false = 0;
      bool negdef = 0;
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
        if (lit == fg.true_branch) {
          found_true++;
          negdef = true;
        }
        if (lit == -fg.true_branch)
          found_true++;
        if (lit == fg.false_branch) {
          found_false++;
          negdef = true;
        }
        if (lit == -fg.false_branch)
          found_false++;
      }
      if (skip)
        continue;
      if (found_true == 2 || found_false == 2) {
        assert (found_true != found_false);
        refactoring.candidates.emplace_back ();
        refactoring.candidates.back ().candidate = c;
        refactoring.candidates.back ().index = index;
        refactoring.candidates.back ().negcon = found_true != 2;
        refactoring.candidates.back ().negdef = negdef;
      }
    }
    index++;
    // drop gate.
    if (found_all_gate_clauses < 4)
      refactoring.gate_clauses.back ().skip = true;
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

  auto &schedule = refactoring.candidates;
  int64_t scheduled = schedule.size ();
  stats.refactorsched += scheduled;

  PHASE ("refactor", stats.refactor,
         "scheduled %" PRId64 " clauses to be refactored %.0f%%", scheduled,
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

  refactoring.ticks = ticks;
  while (!unsat && !terminated_asynchronously () && !schedule.empty () &&
         refactoring.ticks < limit) {
    refactor_candidate cand = schedule.back (); // Next candidate.
    schedule.pop_back ();
    bool suc = refactor_clause (refactoring, cand);
    if (suc)
      stats.refactorsuccs++;
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
  if (factored_gates.empty ())
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
