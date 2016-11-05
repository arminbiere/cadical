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
  if (lim.fixed_at_last_elim == stats.fixed &&
      lim.irredundant_at_last_elim == stats.irredundant) return false;
  return lim.elim <= stats.conflicts;
}

/*------------------------------------------------------------------------*/

bool Internal::have_tautological_resolvent (Clause * c, Clause * d) {
  stats.restests++;
  assert (!c->garbage);
  assert (!d->garbage);
  if (c->size > d->size) swap (c, d);
  LOG (c, "testing resolution with first antecedent");
  LOG (d, "testing resolution with second antecedent");
  mark (c);
  int clashing = 0;
  const const_literal_iterator end = d->end ();
  const_literal_iterator i;
  for (i = d->begin (); clashing < 2 && i != end; i++)
    if (marked (*i) < 0) clashing++;
  unmark (c);
  assert (clashing > 0);
  const bool tautological = (clashing > 1);
#ifdef LOGGING
  if (tautological) LOG ("have tautological resolvent");
  else LOG ("have non-tautological resolvent");
#endif
  return tautological;
}

void Internal::resolve_clauses (Clause * c, Clause * d) {
  stats.resolutions++;
  assert (clause.empty ());
  assert (!c->garbage);
  assert (!d->garbage);
  if (c->size > d->size) swap (c, d);
  LOG (c, "resolving first antecedent");
  LOG (d, "resolving second antecedent");
  const_literal_iterator end = c->end ();
  const_literal_iterator i;
  for (i = c->begin (); i != end; i++) mark (*i);
  int pivot = 0;
  end = d->end ();
  for (i = d->begin (); i != end; i++) {
    const int lit = *i, tmp = marked (lit);
    if (tmp > 0) continue;
    else if (!tmp) clause.push_back (lit);
    else assert (!pivot), pivot = -lit;
  }
  end = c->end ();
  for (i = c->begin (); i != end; i++) {
    const int lit = *i;
    if (lit != pivot) clause.push_back (lit);
    unmark (lit);
  }
}

/*------------------------------------------------------------------------*/

// Check whether the number of non-tautological resolutions on 'pivot' is
// smaller or equal to the number of clauses with 'pivot' or '-pivot'.  This
// is the main criteria of bounded variable elimination.

bool Internal::resolvents_are_bounded (int pivot, vector<Clause*> & res) {

  LOG ("checking whether resolvents on %d are bounded", pivot);

  assert (!val (pivot));
  assert (!eliminated (pivot));

  // Beside determining whether the number of non-tautological resolvents is
  // too large, this function also produces the list of all consecutive
  // pairs of clauses, with non-tautological resolvent such that latter in
  // 'add_resolvents' these can actually be resolved and added.

  res.clear ();               // pairs of non-tautological resolvents
  long count = 0;             // maintain 'count == res.size ()/2'

  Occs & ps = occs (pivot), & ns = occs (-pivot);
  long pos = ps.size (), neg = ns.size ();

  assert (pos <= neg);       // better, but not crucial ...

  // Bound on the number non-tautological resolvents.

  long bound = pos + neg;

  LOG ("try to eliminate %d with %ld = %ld + %ld occurrences",
    pivot, bound, pos, neg);

  // Try all resolutions between a positive occurrence (outer loop) of
  // 'pivot' and a negative occurrence of 'pivot' (inner loop) as long the
  // bound on non-tautological resolvents is not hit and the size of the
  // generated resolvents does not exceed the resolvent size limit.
  //
  const const_clause_iterator pe = ps.end ();
  const_clause_iterator i;
  bool too_long = false;
  for (i = ps.begin (); !too_long && count <= bound && i != pe; i++) {
    Clause * c = *i;
    const const_clause_iterator ne = ns.end ();
    const_clause_iterator j;
    for (j = ns.begin (); !too_long && count <= bound && j != ne; j++) {
      Clause * d = *j;
      if (have_tautological_resolvent (c, d)) continue;
      if (c->size + d->size - 2 > opts.elimclslim) too_long = true;
      else {
        res.push_back (c);
        res.push_back (d);
        count++;
        LOG ("now have %ld non-tautological resolvents", count);
      }
    }
  }
#ifdef LOGGING
  if (too_long)
    LOG ("resolvent exceeds limit on resolvent size");
  else if (count > bound)
    LOG ("found too many %ld non-tautological resolvents on %d",
      count, pivot);
  else
    LOG ("found only %ld <= %ld non-tautological resolvents on %d",
      count, bound, pivot);
#endif
  return !too_long && count <= bound;
}

/*------------------------------------------------------------------------*/

// Go over all consecutive pairs of clauses in 'res', resolve and add them.
// Be careful with empty and unit resolvents and ignore satisfied clauses
// and falsified literals. If units are resolved then propagate them.

inline void Internal::add_resolvents (int pivot,
                                      vector<Clause*> & res,
                                      vector<int> & units) {

  LOG ("adding all %ld resolvents on %d", (long) res.size ()/2, pivot);

  assert (!val (pivot));
  assert (!eliminated (pivot));

  long resolvents = 0;

  const const_clause_iterator end = res.end ();
  const_clause_iterator i = res.begin ();
  while (!unsat && i != end) {
    resolve_clauses (*i++, *i++);
    check_clause ();
    if (clause.empty ()) {
      LOG ("empty resolvent");
      learn_empty_clause ();
    } else if (clause.size () == 1) {
      const int unit = clause[0];
      LOG ("saving unit resolvent %d", unit);
      if (proof) proof->trace_unit_clause (unit);
      units.push_back (unit);
    } else {
      resolvents++;
      Clause * r = new_resolved_irredundant_clause ();
      assert (occs ());
      const const_literal_iterator re = r->end ();
      for (const_literal_iterator l = r->begin (); l != re; l++) {
        Occs & os = occs (*l);
        if (os.empty ()) continue;      // was not connected ...
        occs (*l).push_back (r);
      }
    }
    clause.clear ();
  }

  LOG ("added %ld resolvents to eliminate %d", resolvents, pivot);
}

/*------------------------------------------------------------------------*/

// Remove clauses with 'pivot' and '-pivot' by marking them as garbage and
// at the same time push those with 'pivot' on the extension stack for
// latter witness reconstruction (in 'extend').

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

inline void Internal::elim (int pivot,
                            vector<Clause*> & work,
                            vector<int> & units) {

  // First remove garbage clauses to get a (more) accurate count. There
  // might still be satisfied clauses included in this count which we have
  // not found yet by we ignore this in the following check.
  //
  long pos = flush_occs (pivot);
  long neg = flush_occs (-pivot);

  // If number of occurrences became too large do not eliminate variable.
  //
  if (pos > opts.elimocclim) return;
  if (neg > opts.elimocclim) return;

  // The 'mark_clauses_with_literal_garbage' benefits from having the
  // 'pivot' in the phase with less occurrences than its negation.  It
  // reduces the size of the extension stack greatly.
  //
  if (pos > neg) pivot = -pivot;

  if (!resolvents_are_bounded (pivot, work)) return;

  add_resolvents (pivot, work, units);
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

  backtrack ();
  reset_watches ();

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
  vector<int> units;

  const long old_resolutions = stats.resolutions;
  const int old_eliminated = stats.eliminated;

  // Try eliminating variables according to the schedule.
  //
  const long irredundant_limit = stats.irredundant;
  const const_idx_sum_occs_iterator eos = schedule.end ();
  const_idx_sum_occs_iterator k;
  vector<Clause*> work;
  for (k = schedule.begin (); !unsat && k != eos; k++) {
    if (stats.garbage > irredundant_limit) garbage_collection ();
    elim (k->idx, work, units);
  }

  inc_bytes (bytes_vector (work));
  inc_bytes (bytes_vector (units));

  // Mark all redundant clauses with eliminated variables as garbage.
  //
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

  long resolutions = stats.resolutions - old_resolutions;
  int eliminated = stats.eliminated - old_eliminated;
  VRB ("elim", stats.eliminations,
    "eliminated %ld variables %.0f%% in %ld resolutions %ld units",
    eliminated, percent (eliminated, scheduled),
    resolutions, units.size ());

  dec_bytes (bytes_vector (work));
  dec_bytes (bytes_vector (units));
  dec_bytes (bytes_vector (schedule));
  erase_vector (schedule);
  erase_vector (work);

  if (!units.empty ()) {
    const const_int_iterator eou = units.end ();
    const_int_iterator i;
    for (i = units.begin (); i != eou; i++) {
      int unit = *i;
      const int tmp = val (unit);
      if (tmp < 0) {
        LOG ("found clashing resolved unit %d", unit);
        learn_empty_clause ();
      } else if (tmp > 0) {
        LOG ("ignoring redundant resolved unit %d", unit);
      } else {
        LOG ("assigning resolved unit %d", unit);
        assign (unit);
      }
    }
    if (!unsat && !propagate ()) {
      LOG ("propagating resolved units results in empty clause");
      learn_empty_clause ();
    }
    erase_vector (units);
    garbage_collection ();
  } else account_implicitly_allocated_bytes ();

  lim.subsumptions_at_last_elim = stats.subsumptions;
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

  // Make sure there was an subsumption attempt since last elimination.
  //
  if (lim.subsumptions_at_last_elim == stats.subsumptions)
    subsume_round ();

  for (;;) {
    round++;
    if (!elim_round ()) break;
    if (round >= limit) break;             // stop after elimination
    if (!subsume_round (true)) break;
  }

  int eliminated = stats.eliminated - old_eliminated;
  double relelim = percent (eliminated, old_var);
  VRB ("elim", stats.eliminations,
    "elimination %ld eliminated %d variables %.2f% in %d rounds",
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
  lim.irredundant_at_last_elim = stats.irredundant;
}

};
