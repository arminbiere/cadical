#include "internal.hpp"

namespace CaDiCaL {

// Implements bounded variable elimination as pioneered in our SATeLite
// paper.  This is an inprocessing version, e.g., is interleaved with search
// and triggers subsumption and strengthening rounds during elimination
// rounds.  It focuses only those variables which occurred in removed
// irredundant clauses since the last time an elimination round was run.
// By bounding the maximum number of occurrences and the maximum clause
// size we can run each elimination round until completion.  See the code of
// 'elim' for the actual scheduling of 'subsumption' and 'elimination'.

/*------------------------------------------------------------------------*/

// Note that the new fast subsumption algorithm implemented in 'subsume'
// does not distinguish between irredundant and redundant clauses and is
// also run during search to strengthen and remove 'sticky' redundant
// clauses but also irredundant ones.  So beside learned units during search
// or as consequence of other preprocessors, these subsumption rounds during
// search can remove (irredundant) clauses (and literals), which in turn
// might make new bounded variable elimination possible.  This is tested
// in the 'eliminating' guard.

bool Internal::eliminating () {

  if (!opts.simplify) return false;
  if (!opts.elim) return false;

  // Wait until there has been a change in terms of new units or new removed
  // variables (in removed or shrunken irredundant clauses).
  //
  if (lim.fixed_at_last_elim == stats.all.fixed &&
      lim.removed_at_last_elim == stats.removed) return false;

  // Wait until next 'reduce'.
  //
  if (stats.conflicts != lim.conflicts_at_last_reduce) return false;

  return lim.elim <= stats.conflicts;
}

/*------------------------------------------------------------------------*/

// Update the global elimination schedule 'esched' after adding or removing
// a clause.  Scheduling is based on the two-sided score 'noccs2', which
// needs explicit updates.

inline void Internal::elim_update_added (Clause * c) {
  assert (!c->redundant);
  const const_literal_iterator end = c->end ();
  const_literal_iterator i;
  for (i = c->begin (); i != end; i++) {
    const int lit = *i;
    if (!active (lit)) continue;
    Occs & os = occs (lit);
    if (os.empty ()) continue;          // not connected
    os.push_back (c);
    noccs2 (lit)++;
    const int idx = abs (lit);
    if (esched.contains (idx)) esched.update (idx);
    else {
      LOG ("rescheduling %d for elimination after adding clause", idx);
      esched.push_back (idx);
    }
  }
}

inline void Internal::elim_update_removed (Clause * c, int except) {
  assert (!c->redundant);
  const const_literal_iterator end = c->end ();
  const_literal_iterator i;
  for (i = c->begin (); i != end; i++) {
    const int lit = *i;
    if (lit == except) continue;
    assert (lit != -except);
    if (!active (lit)) continue;
    if (occs (lit).empty ()) continue;          // not connected
    long & score = noccs2 (lit);
    assert (score > 0);
    score--;
    const int idx = abs (lit);
    if (esched.contains (idx)) esched.update (idx);
    else {
      LOG ("rescheduling %d for elimination after removing clause", idx);
      esched.push_back (idx);
    }
  }
}

/*------------------------------------------------------------------------*/

// Resolve two clauses on the pivot literal 'pivot', which is assumed to
// occur in opposite phase in 'c' and 'd'.  The actual resolvent is stored
// in the temporary global 'clause' if it is not redundant.  It is
// considered redundant if one of the clauses is already marked as garbage
// it is root level satisfied, or the resolvent is empty or a unit.  Note
// that current root level assignments are taken into account, e.g., by
// removing root level falsified literals.  The function returns true if the
// resolvent is not redundant and for instance has to be taken into account
// during bounded variable elimination.

bool Internal::resolve_clauses (Clause * c, int pivot, Clause * d) {

  stats.elimres++;

  if (c->garbage || d->garbage) return false;
  if (c->size > d->size) swap (c, d);           // optimize marking
  if (c->size == 2) stats.elimres2++;

  assert (!level);
  assert (clause.empty ());

  int p = 0;               // determine pivot in 'c' for debugging
  int satisfied = 0;       // contains this satisfying literal
  int eliminated = 0;      // contains this eliminated literal

  const_literal_iterator end = c->end ();
  const_literal_iterator i;

  // First determine whether the first antecedent is satisfied, add its
  // literals to 'clause' and mark them (except for 'pivot').
  //
  for (i = c->begin (); !satisfied && !eliminated && i != end; i++) {
    int lit = *i, tmp;
    if (lit == pivot || lit == -pivot) { p = lit; continue; }
    if (flags (lit).eliminated ()) eliminated = lit;
    else if ((tmp = val (lit)) > 0) satisfied = lit;
    else if (tmp < 0) continue;
    else mark (lit), clause.push_back (lit);
  }
  assert (!eliminated);
  if (satisfied) {
    LOG (c, "satisfied by %d antecedent", satisfied);
    if (!c->redundant) elim_update_removed (c);
  }
  if (satisfied || eliminated) {
    mark_garbage (c);
    clause.clear ();
    unmark (c);
    return false;
  }
  assert (p), (void) p; // 'pivot' or '-pivot' has to be in 'c'

  int q = 0;            // pivot in 'd' for debugging purposes
  int tautological = 0; // clashing literal if tautological

  // Then determine whether the second antecedent is satisfied, add its
  // literal to 'clause' and check whether a clashing literal is found, such
  // that the resolvent would be tautological.
  //
  end = d->end ();
  for (i = d->begin ();
       !satisfied && !eliminated && !tautological && i != end;
       i++) {
    int lit = *i, tmp;
    if (lit == pivot || lit == -pivot) { q = lit; continue; }
    if (flags (lit).eliminated ()) eliminated = lit;
    else if ((tmp = val (lit)) > 0) satisfied = lit;
    else if (tmp < 0) continue;
    else if ((tmp = marked (lit)) < 0) tautological = lit;
    else if (!tmp) clause.push_back (lit);
  }

  unmark (c);
  const size_t size = clause.size ();
  if (tautological || satisfied || eliminated || size <= 1) clause.clear ();

  assert (!eliminated);
  if (satisfied) {
    LOG (d, "satisfied by %d antecedent", satisfied);
    if (!d->redundant) elim_update_removed (d);
  }
  if (satisfied || eliminated) {
    mark_garbage (d);
    return false;
  }

  // If the resolvent is not tautological, e.g., we went over all of 'd',
  // then 'd' also has to contain either 'pivot' or '-pivot' which is saved
  // in 'q' and the phase of the pivot has to be the opposite as in 'c'.
  //
  assert (tautological || q == -p), (void) q;

  LOG (c, "first antecedent");
  LOG (d, "second antecedent");

  if (tautological)
    LOG ("resolvent tautological on %d", tautological);
  else if (!size) {
    LOG ("empty resolvent");
    learn_empty_clause ();
  } else if (size == 1) {
    const int unit = clause[0];
    LOG ("unit resolvent %d", unit);
    assign_unit (unit);
  } else LOG (clause, "resolvent");

  return size > 1 && !tautological;
}

/*------------------------------------------------------------------------*/

// Check whether the number of non-tautological resolvents on 'pivot' is
// smaller or equal to the number of clauses with 'pivot' or '-pivot'.  This
// is the main criteria of bounded variable elimination.

bool Internal::elim_resolvents_are_bounded (int pivot, long pos, long neg) {

  LOG ("checking whether resolvents on %d are bounded", pivot);

  assert (!unsat);
  assert (!val (pivot));
  assert (!flags (pivot).eliminated ());

  Occs & ps = occs (pivot), & ns = occs (-pivot);
  assert (pos <= (long) ps.size ());
  assert (neg <= (long) ns.size ());
  assert (pos <= neg);                          // better, but not crucial

  // Bound the number of non-tautological resolvents by the number of
  // positive and negative occurrences, such that the number of clauses to
  // be added is at most the number of removed clauses.
  //
  long bound = pos + neg;
  assert (bound <= noccs2 (pivot)); // not '==' due to 'garbage_collection'

  LOG ("try to eliminate %d with %ld = %ld + %ld occurrences",
    pivot, bound, pos, neg);

  const const_occs_iterator pe = ps.end (), ne = ns.end ();
  const_occs_iterator i, j;

  long pm = 0, nm = 0;

  for (i = ps.begin (); i != pe; i++) {
    Clause * c = *i;
    assert (!c->garbage);
    long tmp = c->size;
    if (tmp > pm) pm = tmp;
  }

  for (j = ns.begin (); j != ne; j++) {
    Clause * d = *j;
    assert (!d->garbage);
    long tmp = d->size;
    if (tmp > nm) nm = tmp;
  }

  if (pm + nm - 2 > opts.elimclslim) {
    LOG ("expecting one resolvent to exceed limit on resolvent size");
    return false;
  }

  // From all 'pos*neg' possible resolvents we need 'needed' many
  // tautological resolvents.  As soon we find a tautological resolvent we
  // decrease 'needed' and as soon it becomes zero or less we can stop
  // resolving, since bounded variable elimination will succeed.
  //
  long needed = pos*neg - bound;

  if (needed > 0) {
    stable_sort (ps.begin (), ps.end (), smaller_size ());
    stable_sort (ns.begin (), ns.end (), smaller_size ());
  }

  long count = 0;               // number of non-tautological resolvents

  // Try all resolutions between a positive occurrence (outer loop) of
  // 'pivot' and a negative occurrence of 'pivot' (inner loop) as long the
  // bound on non-tautological resolvents is not hit and the size of the
  // generated resolvents does not exceed the resolvent size limit.
  //
  for (i = ps.begin (); needed >= 0 && i != pe; i++) {
    Clause * c = *i;
    assert (!c->redundant);
    if (c->garbage) { needed -= neg; continue; }
    for (j = ns.begin (); needed >= 0 && j != ne; j++) {
      Clause * d = *j;
      assert (!d->redundant);
      if (d->garbage) { needed--; continue; }
      stats.elimrestried++;
      if (resolve_clauses (c, pivot, d)) {
        assert (clause.size () <= (size_t) opts.elimclslim);
        clause.clear ();
        if (++count > bound) {
          LOG ("too many %ld non-tautological resolvents on %d",
            count, pivot);
          return false;
        }
        LOG ("now have %ld non-tautological resolvents", count);
      } else if (unsat) return false;
      else needed--;
    }
  }

  if (needed <= 0) LOG ("found enough tautological resolvents");
  else LOG ("expecting %ld <= %ld resolvents", count, bound);

  return true;
}

/*------------------------------------------------------------------------*/

// Add all resolvents on 'pivot' and connect them.

inline void Internal::elim_add_resolvents (int pivot) {

  LOG ("adding all resolvents on %d", pivot);

  assert (!val (pivot));
  assert (!flags (pivot).eliminated ());

  long resolvents = 0;

  Occs & ps = occs (pivot), & ns = occs (-pivot);
  const const_occs_iterator eop = ps.end (), eon = ns.end ();
  const_occs_iterator i, j;
  for (i = ps.begin (); !unsat && i != eop; i++) {
    Clause * c = *i;
    for (j = ns.begin (); !unsat && j != eon; j++) {
      Clause *d = *j;
      if (!resolve_clauses (c, pivot, d)) continue;
      external->check_learned_clause ();
      if (!c->redundant && !d->redundant) {
        resolvents++;
        Clause * r = new_resolved_irredundant_clause ();
        if (!c->redundant && !d->redundant) elim_update_added (r);
      }
      clause.clear ();
    }
  }
  LOG ("added %ld resolvents to eliminate %d", resolvents, pivot);
}

/*------------------------------------------------------------------------*/

// Remove clauses with 'pivot' and '-pivot' by marking them as garbage and
// at the same time push those with 'pivot' on the extension stack for
// witness reconstruction (in 'extend').

inline void Internal::mark_eliminated_clauses_as_garbage (int pivot) {

  assert (!unsat);

  LOG ("marking irredundant clauses with %d as garbage", pivot);

  Occs & ps = occs (pivot);
  const const_occs_iterator pe = ps.end ();
  const_occs_iterator i;
  for (i = ps.begin (); i != pe; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    mark_garbage (c);
    if (c->redundant) continue;
    external->push_clause_on_extension_stack (c, pivot);
    elim_update_removed (c, pivot);
  }
  erase_occs (ps);

  LOG ("marking irredundant clauses with %d as garbage", -pivot);

  Occs & ns = occs (-pivot);
  const const_occs_iterator ne = ns.end ();
  for (i = ns.begin (); i != ne; i++) {
    Clause * d = *i;
    if (d->garbage) continue;
    mark_garbage (d);
    if (d->redundant) continue;
    elim_update_removed (d, -pivot);
  }
  erase_occs (ns);

  // This is a trick by Niklas Soerensson to avoid saving all clauses on the
  // extension stack.  Just first in extending the witness the 'pivot' is
  // forced to false and then if necessary fixed by checking the clauses in
  // which 'pivot' occurs to be falsified.

  external->push_unit_on_extension_stack (-pivot);
}

/*------------------------------------------------------------------------*/

// Try to eliminate 'pivot' by bounded variable elimination.

inline void Internal::try_to_eliminate_variable (int pivot) {

  if (!active (pivot)) return;

  LOG ("trying to eliminate %d", pivot);
  assert (!flags (pivot).eliminated ());

  // First remove garbage clauses to get a (more) accurate count. There
  // might still be satisfied clauses included in this count which we have
  // not found yet but we ignore them in the following check.
  //
  long pos = flush_occs (pivot);
  long neg = flush_occs (-pivot);

  // Bound the number of resolvents tried per variable by '2*elimocclim'.
  //
  if (pos > opts.elimocclim || neg > opts.elimocclim) {
    LOG ("now too many occurrences of %d", pivot);
    return;
  }

  // The 'mark_clauses_with_literal_garbage' benefits from having the
  // 'pivot' in the phase with less occurrences than its negation.  It
  // reduces the size of the extension stack greatly.
  //
  if (pos > neg) pivot = -pivot, swap (pos, neg);

  if (!elim_resolvents_are_bounded (pivot, pos, neg)) {
    LOG ("kept and not eliminated %d", pivot);
    return;
  }

  elim_add_resolvents (pivot);
  if (!unsat) mark_eliminated_clauses_as_garbage (pivot);

  assert (active (pivot));
  flags (pivot).status = Flags::ELIMINATED;
  LOG ("eliminated %d", pivot);
  stats.all.eliminated++;
  stats.now.eliminated++;
}

/*------------------------------------------------------------------------*/

void
Internal::mark_redundant_clauses_with_eliminated_variables_as_garbage () {
  const const_clause_iterator end = clauses.end ();
  const_clause_iterator i;
  for (i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (c->garbage || !c->redundant) continue;
    const const_literal_iterator eol = c->end ();
    const_literal_iterator j;
    for (j = c->begin (); j != eol; j++)
      if (flags (*j).eliminated ()) break;
    if (j != eol) mark_garbage (c);
  }
}

/*------------------------------------------------------------------------*/

bool Internal::elim_round () {

  SWITCH_AND_START (search, simplify, elim);

  stats.eliminations++;
  lim.removed_at_last_elim = stats.removed;

  assert (!level);

  init_noccs2 ();    // two-sided number of irredundant occurrences

  const int size_limit = opts.elimclslim;
  const long nocc2_limit = opts.elimocclim;
  const long nocc2_limit_exceeded = nocc2_limit + 1;

  // First compute the number of occurrences of each literal and at the same
  // time mark satisfied clauses and update 'removed' flags of variables in
  // clauses with root level assigned literals (both false and true).
  //
  const_clause_iterator eoc = clauses.end ();
  const_clause_iterator i;
  for (i = clauses.begin (); i != eoc; i++) {
    Clause * c = *i;
    if (c->garbage || c->redundant) continue;
    const const_literal_iterator eol = c->end ();
    const_literal_iterator j;
    if (c->size > size_limit) {
      LOG (c, "variables not scheduled in too large");
      for (j = c->begin (); j != eol; j++)
        noccs2 (*j) = nocc2_limit_exceeded;        // thus not scheduled
    } else {
      bool satisfied = false, falsified = false;
      for (j = c->begin (); j != eol; j++) {
        const int lit = *j, tmp = val (lit);
        if (tmp > 0) satisfied = true;
        else if (tmp < 0) falsified = true;
        else assert (active (lit));
      }
      if (satisfied) mark_garbage (c);          // more precise counts
      else {
        for (j = c->begin (); j != eol; j++) {
          const int lit = *j;
          if (!active (lit)) continue;
          if (falsified) mark_removed (lit); // simulate unit propagation
          noccs2 (lit)++;
        }
      }
    }
  }

  init_occs ();
  assert (esched.empty ());

  // Now find elimination candidates with small number of occurrences, which
  // do not occur in too large clauses but do occur in clauses which have
  // been removed since the last time we ran bounded variable elimination.
  //
  for (int idx = 1; idx <= max_var; idx++) {
    if (!active (idx)) continue;
    if (!flags (idx).removed) continue;
    const long score = noccs2 (idx);
    if (score > nocc2_limit) continue;
    LOG ("scheduling %d for elimination initially", idx);
    esched.push_back (idx);
  }

  esched.shrink ();

  // We have scheduled all removed variables since last elimination and
  // will now reset their 'removed' flag, so only new removed variables will
  // be considered as candidates in the next elimination.
  //
  reset_removed ();

#ifndef QUIET
  long scheduled = esched.size ();
#endif

  VRB ("elim", stats.eliminations,
    "scheduled %ld variables %.0f%% for elimination",
    scheduled, percent (scheduled, active_variables ()));

  // Connect irredundant clauses with elimination candidates as well as
  // literals occurring in not too many and small enough clauses.
  //
  for (i = clauses.begin (); i != eoc; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    if (c->redundant) continue;
    const const_literal_iterator eol = c->end ();
    const_literal_iterator j;
    for (j = c->begin (); j != eol; j++) {
      const int lit = *j;
      if (!active (lit)) continue;
      const int idx = abs (lit);
      const long score = noccs2 (idx);
      if (score > nocc2_limit) continue;
      occs (lit).push_back (c);
    }
  }

#ifndef QUIET
  const long old_resolutions = stats.elimres;
#endif
  const int old_eliminated = stats.all.eliminated;

  // Limit on garbage bytes during variable elimination. If the limit is hit
  // a garbage collection is performed.
  //
  const long limit = (2*stats.irrbytes/3) + (1<<20);

  // Try eliminating variables according to the schedule.
  //
  while (!unsat && !esched.empty ()) {
    int idx = esched.front ();
    esched.pop_front ();
    flags (idx).removed = false;
    try_to_eliminate_variable (idx);
    if (stats.garbage <= limit) continue;
    mark_redundant_clauses_with_eliminated_variables_as_garbage ();
    garbage_collection ();
  }

  esched.erase ();
  reset_noccs2 ();
  reset_occs ();

  // Mark all redundant clauses with eliminated variables as garbage.
  //
  if (!unsat)
    mark_redundant_clauses_with_eliminated_variables_as_garbage ();

  int eliminated = stats.all.eliminated - old_eliminated;
#ifndef QUIET
  long resolutions = stats.elimres - old_resolutions;
  VRB ("elim", stats.eliminations,
    "eliminated %ld variables %.0f%% in %ld resolutions",
    eliminated, percent (eliminated, scheduled), resolutions);
#endif

  lim.subsumptions_at_last_elim = stats.subsumptions;

  report ('e');

  STOP_AND_SWITCH (elim, simplify, search);

  return !unsat && eliminated > 0;
}

/*------------------------------------------------------------------------*/

void Internal::elim () {

  int old_eliminated = stats.all.eliminated;
  int old_var = active_variables ();

  int round = 0, limit;

  if (stats.eliminations) limit = opts.elimrounds;
  else limit = opts.elimroundsinit;
  assert (limit > 0);

  // Make sure there was a subsumption attempt since last elimination.
  //
  if (lim.subsumptions_at_last_elim == stats.subsumptions)
    subsume ();

  if (level) backtrack ();
  reset_watches ();             // saves lots of memory

  // Alternate variable elimination and subsumption until nothing changes or
  // the round limit is hit.
  //
  for (;;) {
    round++;
    if (!elim_round ()) break;
    if (unsat) break;
    if (round >= limit) break;             // stop after elimination
    long old_removed = stats.removed;
    subsume_round ();
    if (old_removed == stats.removed) break;
  }

  if (!unsat) {
    init_watches ();
    connect_watches ();
  }

  if (unsat) LOG ("elimination derived empty clause");
  else if (propagated < trail.size ()) {
    LOG ("elimination produced %ld units", trail.size () - propagated);
    if (!propagate ()) {
      LOG ("propagating units after elimination results in empty clause");
      learn_empty_clause ();
    }
  }

  int eliminated = stats.all.eliminated - old_eliminated;
  double relelim = percent (eliminated, old_var);
  VRB ("elim", stats.eliminations,
    "eliminated %d variables %.2f%% in %d rounds",
    eliminated, relelim, round);

  // Schedule next elimination based on number of eliminated variables.
  //
  if (relelim >= 10) {
    // Very high percentage 10% eliminated, so use base interval.
    lim.elim = stats.conflicts + opts.elimint;
  } else {
    if (!eliminated) {
      // Nothing eliminated, go into geometric increase.
      inc.elim *= 2;
    } else if (relelim < 5) {
      // Less than 5% eliminated, so go into arithmetic increase.
      inc.elim += opts.elimint;
    } else {
      // Substantial number 5%-10% eliminated, keep interval.
    }
    lim.elim = stats.conflicts + inc.elim;
  }
  VRB ("elim", stats.eliminations,
    "next elimination scheduled in %ld conflicts at %ld conflicts",
    lim.elim - stats.conflicts, lim.elim);

  lim.fixed_at_last_elim = stats.all.fixed;
}

};
