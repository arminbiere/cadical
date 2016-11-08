#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"
#include "profile.hpp"
#include "iterator.hpp"
#include "proof.hpp"

#include <algorithm>

namespace CaDiCaL {

bool Internal::eliminating () {
  if (!opts.elim) return false;

  // Wait until there has been a change in terms of new units or removed
  // irredundant clauses (through subsumption).
  //
  if (lim.fixed_at_last_elim == stats.fixed &&
      lim.touched_at_last_elim == stats.touched) return false;

  return lim.elim <= stats.conflicts;
}

/*------------------------------------------------------------------------*/

// Resolve two clauses on the pivot literal 'pivot', which is assumed to
// occur in opposite phase in 'c' and 'd'.  The actual resolvent is stored
// in the temporary global 'clause' if it is not redundant.  It is
// considered redundant if one of the clauses is already marked as garbage
// it is root level satisfied, or the resolvent is empty or a unit.  Note
// that current root level assignment are taken into account, e.g., by
// removing root level falsified literals.  The function returns true if the
// resolvent is not redundant and for instance has to be taken into account
// during bounded variable elimination.

bool Internal::resolve_clauses (Clause * c, int pivot, Clause * d) {

  stats.resolved++;

  if (c->garbage || d->garbage) return false;
  if (c->size > d->size) swap (c, d);

  if (c->size == 2) stats.resolved2++;

  assert (!level);
  assert (clause.empty ());

  int p = 0;            // pivot in 'c' for debugging purposes

  bool satisfied = false;

  const_literal_iterator end = c->end ();
  const_literal_iterator i;

  // First determine whether the first antecedent is satisfied, add its
  // literal to 'clause' and mark them (except for 'pivot').
  //
  for (i = c->begin (); !satisfied && i != end; i++) {
    const int lit = *i;
    if (lit == pivot || lit == -pivot) { p = lit; continue; }
    const int tmp = val (lit);
    if (tmp > 0) satisfied = true;
    else if (tmp < 0) continue;
    else mark (lit), clause.push_back (lit);
  }
  if (satisfied) {
    LOG (c, "satisfied antecedent");
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
       !satisfied && !tautological && i != end;
       i++) {
    const int lit = *i;
    if (lit == pivot || lit == -pivot) { q = lit; continue; }
    int tmp = val (lit);
    if (tmp > 0) satisfied = true;
    else if (tmp < 0) continue;
    else if ((tmp = marked (lit)) < 0) tautological = lit;
    else if (!tmp) clause.push_back (lit);
  }

  unmark (c);
  const size_t size = clause.size ();
  if (tautological || satisfied || size <= 1) clause.clear ();

  if (satisfied) {
    LOG (d, "satisfied antecedent");
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
    assign (unit);
  } else LOG (clause, "resolvent");

  return size > 1 && !tautological;
}

/*------------------------------------------------------------------------*/

// Check whether the number of non-tautological resolvents on 'pivot' is
// smaller or equal to the number of clauses with 'pivot' or '-pivot'.  This
// is the main criteria of bounded variable elimination.

bool Internal::resolvents_are_bounded (int pivot) {

  LOG ("checking whether resolvents on %d are bounded", pivot);

  assert (!unsat);
  assert (!val (pivot));
  assert (!eliminated (pivot));

  Occs & ps = occs (pivot), & ns = occs (-pivot);
  long pos = ps.size (), neg = ns.size ();
  assert (pos <= neg);                          // better, but not crucial

  // Bound the number of non-tautological resolvents by the number of
  // positive and negative occurrences, such that the number of clauses to
  // be added is at most the number of removed clauses.
  //
  long bound = pos + neg;

  LOG ("try to eliminate %d with %ld = %ld + %ld occurrences",
    pivot, bound, pos, neg);

  // From all 'pos*neg' resolvents we need that many redundant resolvents.
  // If this number becomes zero or less we can eliminate the variable.
  //
  long needed = pos*neg - bound;

  long count = 0;               // number of non-tautological resolvents

  // Try all resolutions between a positive occurrence (outer loop) of
  // 'pivot' and a negative occurrence of 'pivot' (inner loop) as long the
  // bound on non-tautological resolvents is not hit and the size of the
  // generated resolvents does not exceed the resolvent size limit.
  //
  const const_clause_iterator pe = ps.end (), ne = ns.end ();
  const_clause_iterator i, j;
  for (i = ps.begin (); needed >= 0 && i != pe; i++) {
    Clause * c = *i;
    if (c->garbage) { needed -= neg; continue; }
    for (j = ns.begin (); needed >= 0 && j != ne; j++) {
      Clause * d = *j;
      if (d->garbage) { needed--; continue; }
      stats.restried++;
      if (resolve_clauses (c, pivot, d)) {
        const int size = (int) clause.size ();
        clause.clear ();
        if (size > opts.elimclslim) {
          LOG ("resolvent exceeds limit on resolvent size");
          return false;
        }
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

  if (needed <= 0) LOG ("found enough redundant resolvents");
  else LOG ("expecting %ld <= %ld resolvents", count, bound);

  return true;
}

/*------------------------------------------------------------------------*/

// Add all resolvents on 'pivot' and connect them.

inline void Internal::add_resolvents (int pivot) {

  LOG ("adding all resolvents on %d", pivot);

  assert (!val (pivot));
  assert (!eliminated (pivot));

  long resolvents = 0;

  Occs & ps = occs (pivot), & ns = occs (-pivot);
  const const_clause_iterator eop = ps.end (), eon = ns.end ();
  const_clause_iterator i, j;
  for (i = ps.begin (); !unsat && i != eop; i++) {
    for (j = ns.begin (); !unsat && j != eon; j++) {
      if (resolve_clauses (*i, pivot, *j)) {
        resolvents++;
        Clause * r = new_resolved_irredundant_clause ();
        const const_literal_iterator re = r->end ();
        for (const_literal_iterator l = r->begin (); l != re; l++) {
          Occs & os = occs (*l);
          if (os.empty ()) continue;      // was not connected ...
          occs (*l).push_back (r);
        }
        clause.clear ();
      }
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
  const const_clause_iterator pe = ps.end ();
  const_clause_iterator i;
  for (i = ps.begin (); i != pe; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    extension.push_back (0);
    const const_literal_iterator end = c->end ();
    const_literal_iterator l;
    extension.push_back (pivot);
    for (l = c->begin (); l != end; l++)
      if (*l != pivot) extension.push_back (*l);
    mark_garbage (c);
  }
  erase_vector (ps);

  LOG ("marking irredundant clauses with %d as garbage", -pivot);

  Occs & ns = occs (-pivot);
  const const_clause_iterator ne = ns.end ();
  for (i = ns.begin (); i != ne; i++)
    if (!(*i)->garbage) mark_garbage (*i);
  erase_vector (ns);

  // This is a trick by Niklas Soerensson to avoid saving all clauses on the
  // extension stack.  Just first in extending the witness the 'pivot' is
  // forced to false and then if necessary fixed by checking the clauses in
  // which 'pivot' occurs to be falsified.

  extension.push_back (0);
  extension.push_back (-pivot);
}

/*------------------------------------------------------------------------*/

// Try to eliminate 'pivot' by bounded variable elimination.

inline void Internal::elim_variable (int pivot) {

  if (val (pivot)) return;

  LOG ("trying to eliminate %d", pivot);
  assert (!eliminated (pivot));

  // First remove garbage clauses to get a (more) accurate count. There
  // might still be satisfied clauses included in this count which we have
  // not found yet but we ignore them in the following check.
  //
  long pos = flush_occs (pivot);
  long neg = flush_occs (-pivot);

  // If number of occurrences became too large do not eliminate variable.
  //
  if (pos > opts.elimocclim || neg > opts.elimocclim) {
    LOG ("now too many occurrences of %d", pivot);
    return;
  }

  // The 'mark_clauses_with_literal_garbage' benefits from having the
  // 'pivot' in the phase with less occurrences than its negation.  It
  // reduces the size of the extension stack greatly.
  //
  if (pos > neg) pivot = -pivot;

  if (!resolvents_are_bounded (pivot)) {
    LOG ("kept and not eliminated %d", pivot);
    return;
  }

  add_resolvents (pivot);
  if (!unsat) mark_eliminated_clauses_as_garbage (pivot);

  LOG ("eliminated %d", pivot);
  eliminated (pivot) = true;
  stats.eliminated++;
}

/*------------------------------------------------------------------------*/

// Sorting the scheduled variables is way faster if we compute the sum of
// the occurrences up-front and avoid pointer access to 'noccs' during
// sorting. This slightly increases the schedule size though.

struct IdxSumOccs {
  int idx;
  long soccs;
  IdxSumOccs (int i, long pos, long neg) : idx (i), soccs (pos + neg) { }
  IdxSumOccs () { }
};

typedef vector<IdxSumOccs>::const_iterator const_idx_sum_occs_iterator;
typedef vector<IdxSumOccs>::iterator idx_sum_occs_iterator;

struct idx_sum_occs_smaller {
  bool operator () (const IdxSumOccs & a, const IdxSumOccs & b) const {
    return a.soccs < b.soccs;
  }
};

/*------------------------------------------------------------------------*/

bool Internal::elim_round () {

  SWITCH_AND_START (search, simplify, elim);
  stats.eliminations++;

  long old_touched = stats.touched;
  long last_touched = lim.touched_at_last_elim;

  backtrack ();
  reset_watches ();             // saves lots of memory

  if (lim.fixed_at_last_collect < stats.fixed) garbage_collection ();
  else account_implicitly_allocated_bytes ();

  vector<IdxSumOccs> schedule;  // schedule of candidate variables
  init_noccs ();                // number of irredundant occurrences

  const int size_limit = opts.elimclslim;
  const long occ_limit = opts.elimocclim;
  const long occ_limit_exceeded = occ_limit + 1;

  // First compute the number of occurrences of each literal.
  //
  const_clause_iterator eoc = clauses.end ();
  const_clause_iterator i;
  for (i = clauses.begin (); i != eoc; i++) {
    Clause * c = *i;
    if (c->garbage || c->redundant) continue;
    const const_literal_iterator eol = c->end ();
    const_literal_iterator j;
    if (c->size > size_limit)
      for (j = c->begin (); j != eol; j++)
        noccs (*j) = occ_limit_exceeded;        // thus not scheduled
    else
      for (j = c->begin (); j != eol; j++)
        if (!val (*j)) noccs (*j)++;
  }

  char * connected;
  NEW (connected, char, max_var + 1);
  ZERO (connected, char, max_var + 1);

  // Now find elimination candidates (with small number of occurrences).
  //
  for (int idx = 1; idx <= max_var; idx++) {
    if (val (idx)) continue;
    if (eliminated (idx)) continue;
    if (touched (idx) <= last_touched &&
        touched (-idx) <= last_touched) continue;
    long pos = noccs (idx);
    if (pos > occ_limit) continue;
    long neg = noccs (-idx);
    if (neg > occ_limit) continue;
    connected [idx] = 1;
    schedule.push_back (IdxSumOccs (idx, pos, neg));
  }
  shrink_vector (schedule);
  reset_noccs ();

  stable_sort (schedule.begin (), schedule.end (), idx_sum_occs_smaller ());

  // Drop 'opts.elimignore' fraction of variables.
  //
  size_t ignore = (1 - opts.elimignore) * schedule.size ();
  if (ignore < schedule.size ()) {
    const long limit = schedule[ignore].soccs;
    while (++ignore < schedule.size () && schedule[ignore].soccs == limit)
      ;
    for (size_t i = ignore; i < schedule.size (); i++)
      connected [ schedule [i].idx ] = 0;
    schedule.resize (ignore);
    shrink_vector (schedule);
  }

  inc_bytes (bytes_vector (schedule));

  long scheduled = schedule.size ();

  VRB ("elim", stats.eliminations,
    "scheduled %ld variables %.0f%% for elimination",
    scheduled, percent (scheduled, active_variables ()));

  init_occs ();

  // Connect irredundant clauses ignoring literals with too many occurrences
  // as well as those occurring in very long irredundant clauses.
  //
  for (i = clauses.begin (); i != eoc; i++) {
    Clause * c = *i;
    if (c->garbage || c->redundant) continue;
    const const_literal_iterator eol = c->end ();
    const_literal_iterator j;
    for (j = c->begin (); j != eol; j++) {
      if (val (*j)) continue;
      if (!connected [abs (*j)]) continue;
      Occs & os = occs (*j);
      assert ((long) os.size () < occ_limit);
      os.push_back (c);
    }
  }

  DEL (connected, char, max_var + 1);

  const long old_resolutions = stats.resolved;
  const int old_eliminated = stats.eliminated;

  // Try eliminating variables according to the schedule.
  //
  const long irredundant_limit = stats.irredundant;
  const const_idx_sum_occs_iterator eos = schedule.end ();
  const_idx_sum_occs_iterator k;
  for (k = schedule.begin (); !unsat && k != eos; k++) {
    if (stats.garbage > irredundant_limit) garbage_collection ();
    elim_variable (k->idx);
  }

  // Mark all redundant clauses with eliminated variables as garbage.
  //
  if (!unsat) {
    eoc = clauses.end ();
    for (i = clauses.begin (); i != eoc; i++) {
      Clause * c = *i;
      if (c->garbage || !c->redundant) continue;
      const const_literal_iterator eol = c->end ();
      const_literal_iterator j;
      for (j = c->begin (); j != eol; j++)
        if (this->eliminated (*j)) break;
      if (j != eol) mark_garbage (c);
    }

    reset_occs ();
    garbage_collection ();

    init_watches ();
    connect_watches ();
  }

  long resolutions = stats.resolved - old_resolutions;
  int eliminated = stats.eliminated - old_eliminated;
  VRB ("elim", stats.eliminations,
    "eliminated %ld variables %.0f%% in %ld resolutions",
    eliminated, percent (eliminated, scheduled), resolutions);

  dec_bytes (bytes_vector (schedule));
  erase_vector (schedule);

  if (unsat) LOG ("elimination derived empty clause");
  else if (propagated < trail.size ()) {
    LOG ("elimination produced %ld units", trail.size () - propagated);
    if (!propagate ()) {
      LOG ("propagating units results in empty clause");
      learn_empty_clause ();
    }
    garbage_collection ();
  } else account_implicitly_allocated_bytes ();

  lim.subsumptions_at_last_elim = stats.subsumptions;
  lim.touched_at_last_elim = old_touched;

  report ('e');

  STOP_AND_SWITCH (elim, simplify, search);

  return !unsat && eliminated > 0;
}

/*------------------------------------------------------------------------*/

void Internal::elim () {

  int old_eliminated = stats.eliminated;
  int old_var = active_variables ();

  int round = 0, limit;

  if (stats.eliminations) limit = opts.elimrounds;
  else limit = opts.elimroundsinit;
  assert (limit > 0);

  // Make sure there was a subsumption attempt since last elimination.
  //
  if (lim.subsumptions_at_last_elim == stats.subsumptions)
    subsume_round ();

  // Alternate variable elimination and subsumption until nothing changes.
  //
  for (;;) {
    round++;
    if (!elim_round ()) break;
    if (round >= limit) break;             // stop after elimination
    if (!subsume_round (true)) break;
  }

  int eliminated = stats.eliminated - old_eliminated;
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

  lim.fixed_at_last_elim = stats.fixed;
}

};
