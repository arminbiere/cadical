#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"
#include "profile.hpp"
#include "iterator.hpp"

#include <algorithm>

namespace CaDiCaL {

bool Internal::eliminating () {
  if (!opts.elim) return false;
  if (lim.fixed_at_last_elim == stats.fixed &&
      lim.irredundant_at_last_elim == stats.irredundant) return false;
  return lim.elim <= stats.conflicts;
}

/*------------------------------------------------------------------------*/

// Check whether the number of non-tautological resolutions on 'pivot' is
// smaller or equal to the number of clauses with 'pivot' or '-pivot'.  This
// is the main criteria of bounded variable elimination.

inline bool
Internal::resolvents_are_bounded (int pivot, vector<Clause*> & res) {

  LOG ("checking whether resolvents on %d are bounded", pivot);

  if (val (pivot)) return false;        // ignore root level assigned
  assert (!eliminated (pivot));

  // Beside determining whether the number of non-tautological resolvents is
  // too large, this function also produce the list of all consecutive pairs
  // of clauses, with non-tautological resolvent such that latter in
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
  // bound on non-tautological resolvents is not hit.
  //
  const const_clause_iterator pe = ps.end ();
  const_clause_iterator i;
  for (i = ps.begin (); count <= bound && i != pe; i++) {

    Clause * c = *i;
    assert (!c->garbage);
    // if (c->garbage) continue;  // redundant!!

    // Check whether first antecedent is not root level satisfied already
    // and at the same time mark all its literals, such that we can easily
    // find tautological resolvents latter when resolving against clauses
    // with negative occurrence of the 'pivot' in the following inner loop.
    //
    const const_literal_iterator ce = c->end ();
    const_literal_iterator l;
    bool satisfied = false;
    for (l = c->begin (); !satisfied && l != ce; l++) {
      int lit = *l;
      if (lit == pivot) continue;
      if (val (lit) > 0) satisfied = true;
      else mark (lit);
    }
    if (satisfied) {
      LOG (c, "skipping satisfied first antecedent");
      mark_garbage (c);
      unmark (c);
      continue;
    }

    LOG (c, "trying first antecedent");

    // In the inner loop we go over all potential resolution candidates
    // which contain '-pivot' and try to resolve them with the first
    // antecedent (on 'pivot').
    //
    const const_clause_iterator ne = ns.end ();
    const_clause_iterator j;
    for (j = ns.begin (); count <= bound && j != ne; j++) {

      Clause * d = *j;
      if (d->garbage) continue;

      // Go over the literals in the second antecedent and check whether
      // they make the resolvent clause satisfied or tautological ignoring
      // root level units fixed to false.
      //
      const const_literal_iterator de = d->end ();
      bool tautological = false;
      satisfied = false;
      for (l = d->begin (); !satisfied && l != de; l++) {
        int lit = *l;
        assert (lit != pivot);
        if (lit == -pivot) continue;
        int tmp = val (lit);
        if (tmp < 0) continue;
        else if (tmp > 0) satisfied = true;
        else if ((tmp = marked (lit)) > 0) continue;
        else if (tmp < 0) tautological = true;
      }
      if (satisfied) {
        LOG (d, "skipping satisfied second antecedent");
        mark_garbage (d);
        continue;
      }

      // Now we count it as a real resolution. Note that those 'satisfied'
      // second antecedent clauses detected above are traversed only once.
      //
      LOG (d, "trying second antecedent");
      stats.resolutions++;

      if (tautological) LOG ("tautological resolvent");
      else {
        count++;
        res.push_back (c);
        res.push_back (d);
        LOG ("now have %ld non-tautological resolvents", count);
      }
    }

    unmark (c);
  }
#ifndef LOGGING
  if (count > bound)
    LOG ("found too many %ld non-tautological resolvents on %d",
      count, pivot);
  else
    LOG ("found only %ld <= %ld non-tautological resolvents on %d",
      count, limit, pivot);
#endif
  return count <= bound;
}

/*------------------------------------------------------------------------*/

// Go over all consecutive pairs of clauses in 'res', resolve and add them.
// Be careful with empty and unit resolvents and ignore satisfied clauses
// and falsified literals. If units are resolved then propagate them.

inline void Internal::add_resolvents (int pivot, vector<Clause*> & res) {

  LOG ("adding all %ld resolvents on %d", (long) res.size ()/2, pivot);

  assert (!val (pivot));
  assert (!eliminated (pivot));

  long resolvents = 0;

  const const_clause_iterator re = res.end ();
  const_clause_iterator i = res.begin ();
  while (!unsat && i != re) {

    Clause * c = *i++, * d = *i++;

    if (c->garbage || d->garbage) continue;
    if (c->size > d->size) swap (c, d);
    assert (clause.empty ());

    // First add all (non-falsified) literals from 'c' and mark them.
    //
    const const_literal_iterator ce = c->end ();
    const_literal_iterator l;
    bool satisfied = false;
    for (l = c->begin (); !satisfied && l != ce; l++) {
      const int lit = *l;
      if (lit == pivot || lit == -pivot) continue;
      const int tmp = val (lit);
      if (tmp > 0) satisfied = true;
      else if (!tmp) clause.push_back (lit), mark (lit);
    }
    if (satisfied) {
      LOG (c, "first now satisfied antecedent");
      mark_garbage (c);
    } else {
      // Now add all (non-falsified) literals from 'd' without duplicates.
      //
      const const_literal_iterator de = d->end ();
      for (l = d->begin (); !satisfied && l != de; l++) {
        const int lit = *l;
        if (lit == pivot || lit == -pivot) continue;
        int tmp = val (lit);
        if (tmp > 0) satisfied = true;
        else if (!tmp) {
          tmp = marked (lit);
          if (!tmp) clause.push_back (lit);
          else assert (tmp > 0);
        }
      }
      if (satisfied) {
        LOG (d, "second now satisfied antecedent");
        mark_garbage (d);
      } else {

        LOG (c, "resolving first antecedent");
        LOG (d, "resolving second antecedent");

	check_clause ();

        if (clause.empty ()) {
          LOG ("empty resolvent");
          learn_empty_clause ();
        } else if (clause.size () == 1) {
          const int unit = clause[0];
          LOG ("unit resolvent %d", unit);
          assign (unit);
          if (!propagate ()) {
            LOG ("propagating resolved unit produces conflict");
            learn_empty_clause ();
          }
        } else {
          resolvents++;
          Clause * r = new_resolved_irredundant_clause ();
	  if (occs ()) {
	    const const_literal_iterator re = r->end ();
	    for (l = r->begin (); l != re; l++) {
	      Occs & os = occs (*l);
	      if (os.empty ()) continue;	// was not connected ...
	      occs (*l).push_back (r);
	    }
	  }
        }
      }
    }
    clause.clear ();
    unmark (c);
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
  erase_vector (watches (pivot));

  LOG ("marking irredundant clauses with %d as garbage", -pivot);

  Occs & ns = occs (-pivot);
  const const_clause_iterator ne = ns.end ();
  for (i = ns.begin (); i != ne; i++)
    if (!(*i)->garbage) mark_garbage (*i);
  erase_vector (ns);
  erase_vector (watches (-pivot));

  // This is a trick by Niklas Soerensson to avoid saving all clauses on the
  // extension stack.  Just first in extending the witness the 'pivot' is
  // forced to false and then if necessary fixed by checking the clauses in
  // which 'pivot' occurs to be falsified.

  extension.push_back (0);
  extension.push_back (-pivot);
}

/*------------------------------------------------------------------------*/

// Try to eliminate 'pivot' by bounded variable elimination.

inline void Internal::elim (int pivot, vector<Clause*> & work) {

  // First remove garbage clauses to get a (more) accurate count. There
  // might still be satisfied clauses included in this count which we have
  // not found yet by we ignore this in the following check.
  //
  long pos = flush_occs (pivot);
  long neg = flush_occs (-pivot);

  // If the number of occurrences it too large do not eliminate variable.
  //
  if (pos > opts.elimocclim) return;
  if (neg > opts.elimocclim) return;

  // Both 'resolvents_bounded' and 'mark_clauses_with_literal_garbage'
  // benefit from having the 'pivot' in the phase with less occurrences than
  // its negation.  For the former this requires less marking and for the
  // latter it reduces the size of the extension stack greatly.
  //
  if (pos > neg) pivot = -pivot;

  if (!resolvents_are_bounded (pivot, work)) return;

  add_resolvents (pivot, work);
  if (!unsat) mark_eliminated_clauses_as_garbage (pivot);

  LOG ("eliminated %d", pivot);
  eliminated (pivot) = true;
  stats.eliminated++;
}

/*------------------------------------------------------------------------*/

bool Internal::elim_round () {

  SWITCH_AND_START (search, simplify, elim);
  stats.eliminations++;

  backtrack ();

  if (lim.fixed_at_last_collect < stats.fixed) garbage_collection ();

  // Allocate schedule, working stack and occurrence lists.
  //
  vector<int> schedule;         // schedule of candidate variables
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
	noccs (*j) = occ_limit_exceeded;	// thus not scheduled
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
    if (noccs (idx) > occ_limit) continue;
    if (noccs (-idx) > occ_limit) continue;
    connected [idx] = 1;
    schedule.push_back (idx);
  }

  // And sort according to the number of occurrences.
  //
  stable_sort (schedule.begin (), schedule.end (), sum_occs_smaller (this));

  // Now prune the schedule above the median.
  //
  size_t ignore = (1 - opts.elimignore) * schedule.size ();
  if (ignore < schedule.size ()) {
    const int idx = schedule[ignore];
    const long median_noccs_sum = noccs (idx) + noccs (-idx);
    while (++ignore < schedule.size ()) {
      const int other = schedule[ignore];
      const long noccs_sum = noccs (other) + noccs (-other);
      if (noccs_sum > median_noccs_sum) break;
    }
    for (size_t i = ignore; i < schedule.size (); i++)
      connected [ abs (schedule [i]) ] = 0;
    schedule.resize (ignore);
    shrink_vector (schedule);
  }

  inc_bytes (bytes_vector (schedule));
  reset_noccs ();

  long scheduled = schedule.size ();
  inc_bytes (bytes_vector (schedule));
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

  const long old_resolutions = stats.resolutions;
  const int old_eliminated = stats.eliminated;

  // Try eliminating variables according to the schedule.
  //
  const long irredundant_limit = stats.irredundant;
  const const_int_iterator eos = schedule.end ();
  const_int_iterator k;
  vector<Clause*> work;
  for (k = schedule.begin (); !unsat && k != eos; k++) {
    if (stats.garbage > irredundant_limit) garbage_collection ();
    elim (*k, work);
  }

  // Account memory for 'work'.
  //
  inc_bytes (bytes_vector (work));

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
  garbage_collection ();

  long resolutions = stats.resolutions - old_resolutions;
  int eliminated = stats.eliminated - old_eliminated;
  VRB ("elim", stats.eliminations,
    "eliminated %ld variables %.0f%% in %ld resolutions",
    eliminated, percent (eliminated, scheduled), resolutions);

  // Release occurrence lists, and both schedule and work stacks.
  //
  reset_occs ();
  dec_bytes (bytes_vector (work));
  dec_bytes (bytes_vector (schedule));
  erase_vector (schedule);
  erase_vector (work);

  report ('e');
  STOP_AND_SWITCH (elim, simplify, search);

  return eliminated > 0;
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
  if (lim.subsumptions_at_last_elim < stats.subsumptions)
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
  lim.subsumptions_at_last_elim = stats.subsumptions;
}

};
