#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"
#include "profile.hpp"
#include "iterator.hpp"

#include <algorithm>

namespace CaDiCaL {

bool Internal::eliminating () {
  if (!opts.elim) return false;

  // Only perform variable elimination immediately after a clause
  // reduction where the overall allocated memory is small.
  //
  if (stats.conflicts != lim.conflicts_at_last_reduce) return false;

  return lim.elim <= stats.conflicts;
}

/*------------------------------------------------------------------------*/

// Remove clauses marked as garbage from the occurrence lists.  This gives
// (more) accurate counts of remaining clauses for variable elimination.

inline size_t Internal::flush_occs (int lit) {
  vector<Clause *> & os = occs[lit];
  const const_clause_iterator end = os.end ();
  const_clause_iterator i;
  clause_iterator k = os.begin ();
  for (i = k; i != end; i++)
    if ((*k++ = *i)->garbage) k--;
  size_t res = k - os.begin ();
  os.resize (res);
  return res;
}

/*------------------------------------------------------------------------*/

// Check whether the number of non-tautological resolutions on 'pivot' is
// smaller or equal to the number of clauses with 'pivot' or '-pivot'.  This
// is the main criteria of bounded variable elimination.

inline bool
Internal::resolvents_bounded (int pivot, vector<Clause*> & res) {

  LOG ("checking whether resolvents on %d are bounded", pivot);

  if (val (pivot)) return false;        // ignore root level assigned
  assert (!eliminated (pivot));

  // Beside determining whether the number of non-tautological resolvents is
  // too large, this function also produce the list of all consecutive pairs
  // of clauses, with non-tautological resolvent such that latter in
  // 'add_resolvents' these can actually be resolved and added.

  res.clear ();               // pairs of non-tautological resolvents
  long count = 0;             // maintain 'count == res.size ()/2'

  vector<Clause*> & ps = occs[pivot], & ns = occs[-pivot];
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

      // Now we count it as a real resolution. Note that 'satisfied' second
      // antecedent clauses are traversed only once.
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
      int lit = *l;
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
	int lit = *l;
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

	if (clause.empty ()) {
	  LOG ("empty resolvent");
	  learn_empty_clause ();
	} else if (clause.size () == 1) {
	  int unit = clause[0];
	  LOG ("unit resolvent %d", unit);
	  assign (unit);
	  if (!propagate ()) {
	    LOG ("propagating resolved unit produces conflict");
	    learn_empty_clause ();
	  }
	} else {
	  resolvents++;
	  Clause * r = new_resolved_irredundant_clause ();
	  const const_literal_iterator re = d->end ();
	  for (l = r->begin (); l != re; l++)
	    occs[*l].push_back (r);
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

inline void Internal::mark_clauses_with_literal_garbage (int pivot) {
  assert (!unsat);

  LOG ("marking irredundant clauses with %d as garbage", pivot);

  vector<Clause*> & ps = occs[pivot];
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

  LOG ("marking irredundant clauses with %d as garbage", -pivot);

  vector<Clause*> & ns = occs[pivot];
  const const_clause_iterator ne = ns.end ();
  for (i = ns.begin (); i != ne; i++)
    if (!(*i)->garbage) mark_garbage (*i);

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
  // not found yet.
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

  if (!resolvents_bounded (pivot, work)) return;

  add_resolvents (pivot, work);
  if (!unsat) mark_clauses_with_literal_garbage (pivot);

  LOG ("eliminated %d", pivot);
  eliminated (pivot) = true;
  stats.eliminated++;
}

/*------------------------------------------------------------------------*/

void Internal::elim () {

  SWITCH_AND_START (search, simplify, elim);
  stats.eliminations++;

  // Otherwise lots of contracts fail.
  //
  backtrack ();

  // Allocate schedule, working stack and occurrence lists.
  //
  vector<int> schedule;
  vector<Clause*> work;
  init_occs ();

  // Connect all irredundant clauses.
  //
  const const_clause_iterator eoc = clauses.end ();
  const_clause_iterator i;
  for (i = clauses.begin (); i != eoc; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    if (c->redundant) continue;
    const const_literal_iterator eol = c->end ();
    const_literal_iterator j;
    for (j = c->begin (); j != eol; j++) {
      int lit = *j;
      assert (!val (lit));
      occs[lit].push_back (c);
    }
  }

  // Now find elimination candidates.
  //
  for (int idx = 1; idx <= max_var; idx++) {
    if (val (idx)) continue;
    if (eliminated (idx)) continue;
    if (occs[idx].size () > (size_t) opts.elimocclim) continue;
    if (occs[-idx].size () > (size_t) opts.elimocclim) continue;
    schedule.push_back (idx);
  }
  inc_bytes (VECTOR_BYTES (schedule));
  VRB ("scheduled %ld variables for elimination",
    (long) schedule.size ());

  account_occs ();  // Compute and account memory for 'occs'.

  // And sort according to the number of occurrences.
  //
  stable_sort (schedule.begin (), schedule.end (), sum_occs_smaller (this));

  long old_resolutions = stats.resolutions;
  int old_eliminated = stats.eliminated;

  // Try eliminating variables according to the schedule.
  //
  const const_int_iterator eos = schedule.end ();
  const_int_iterator k;
  for (k = schedule.begin (); !unsat && k != eos; k++) {
    elim (*k, work);		
    // TODO garbage collection once in a while.
  }

  // Compute and account memory for 'work' and 'occs'.
  //
  inc_bytes (VECTOR_BYTES (work));
  account_occs ();  

  long resolutions = stats.resolutions - old_resolutions;
  int eliminated = stats.eliminated - old_eliminated;
  VRB ("eliminated %ld variables in %ld resolutions",
    eliminated, resolutions);

  // Release occurrence lists, and both schedule and work stacks.
  //
  reset_occs ();
  dec_bytes (VECTOR_BYTES (work));
  dec_bytes (VECTOR_BYTES (schedule));
  schedule = vector<int> ();
  work = vector<Clause*> ();

  // Mark all redundant clauses with eliminated variables as garbage.
  //
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

  inc.elim *= 2;
  lim.elim = stats.conflicts + inc.elim;

  report ('e');
  STOP_AND_SWITCH (elim, simplify, search);
}

};
