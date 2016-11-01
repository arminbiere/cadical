#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"
#include "profile.hpp"
#include "iterator.hpp"

#include <algorithm>

namespace CaDiCaL {

bool Internal::eliminating () {
  if (!opts.elim) return false;
  if (stats.conflicts != lim.conflicts_at_last_reduce) return false;
  return lim.elim <= stats.conflicts;
}

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

inline void
Internal::elim_var (int pivot, vector<int> & work, vector<int> & units) {
  long pos = flush_occs (pivot);
  long neg = flush_occs (-pivot);
  if (pos > opts.elimocclim) return;
  if (neg > opts.elimocclim) return;
  if (pos > neg) { swap (pos, neg); pivot = -pivot; }
  vector<Clause*> & ps = occs[pivot];
  vector<Clause*> & ns = occs[-pivot];
  long limit = pos + neg, count = 0;
  LOG ("try to eliminate %d with %ld = %ld + %ld occurrences",
    pivot, limit, pos, neg);
  work.clear ();
  bool failed = false;
  const_clause_iterator i;
  for (i = ps.begin (); !failed && i != ps.end (); i++) {
    Clause * c = *i;
    LOG (c, "first antecedent");
    mark (c);
    const_clause_iterator j;
    for (j = ns.begin (); !failed && j != ns.end (); j++) {
      Clause * d = *j;
      stats.resolutions++;
      LOG (d, "second antecedent");
      size_t before = work.size ();
      bool tautology = false;
      int unit = 0;
      const_literal_iterator end = d->end (), l;
      for (l = d->begin (); !tautology && l != end; l++) {
	int lit = *l;
	assert (lit != pivot);
	if (lit == -pivot) continue;
	int tmp = marked (lit);
	if (!unit) unit = lit;
	if (tmp > 0) continue;
	else if (tmp < 0) tautology = true;
	else work.push_back (lit);
      }
      int size = c->size - 1 + (int) (work.size () - before);
      if (tautology) {
	LOG ("tautological resolvent");
	work.resize (before);
      } else if (size > opts.elimclslim) {
	LOG ("non-tautological resolvent of size %d too big", size);
	failed = true;
      } else if (size == 1) {
	LOG ("unit %d resolvent", unit);
	units.push_back (unit);
	work.resize (before);
      } else if (++count > limit) { 
	LOG ("limit %ld non-tautological resolvents exhausted", limit);
	failed = true;
      } else {
	LOG ("non-tautological size %d resolvent", size);
	end = c->end ();
	for (l = c->begin (); l != end; l++)
	  if (*l != pivot) work.push_back (*l);
	work.push_back (0);
      }
    }
    unmark (c);
  }
  if (failed) { LOG ("failed to eliminate %d", pivot); return; }
  LOG ("adding %ld resolvents", count);
  const_int_iterator w;
  assert (clause.empty ());
  for (w = work.begin (); w != work.end (); w++) {
    int lit = *w;
    if (lit) clause.push_back (lit);
    else new_resolved_irredundant_clause (), clause.clear ();
  }
  assert (clause.empty ());
  LOG ("marking %ld original clauses as garbage", limit);
  for (i = ps.begin (); i != ps.end (); i++) {
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
  extension.push_back (0);
  extension.push_back (-pivot);
  for (i = ns.begin (); i != ns.end (); i++)
    if (!(*i)->garbage) mark_garbage (*i);
  LOG ("eliminated %d", pivot);
  eliminated (pivot) = true;
  stats.eliminated++;
}

void Internal::elim () {

  SWITCH_AND_START (search, simplify, elim);
  stats.eliminations++;

  // Otherwise lots of contracts fail.
  //
  backtrack ();

  // Allocate schedule and occurrence lists.
  //
  vector<int> schedule, work, units;
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
  account_occs ();

  // Now find elimination candidates.
  //
  for (int idx = 1; idx <= max_var; idx++) {
    if (val (idx)) continue;
    if (eliminated (idx)) continue;
    if (occs[idx].empty () && occs[-idx].empty ()) continue;
    schedule.push_back (idx);
  }
  inc_bytes (VECTOR_BYTES (schedule));
  VRB ("scheduled %ld variables for elimination",
    (long) schedule.size ());

  // And sort according to the number of occurrences.
  //
  stable_sort (schedule.begin (), schedule.end (), sum_occs_smaller (this));

  long old_resolutions = stats.resolutions;
  int old_eliminated = stats.eliminated;

  // Try eliminating variables according to the schedule.
  const const_int_iterator eos = schedule.end ();
  const_int_iterator k;
  for (k = schedule.begin (); k != eos; k++) {
    elim_var (*k, work, units);			
    // TODO garbage collection!
  }

  inc_bytes (VECTOR_BYTES (work));
  inc_bytes (VECTOR_BYTES (units));

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
  work = vector<int> ();

  // Mark all redundant clauses with eliminated variables as garbage.
  //
  for (i = clauses.begin (); i != eoc; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    if (!c->redundant) continue;
    const const_literal_iterator eol = c->end ();
    const_literal_iterator j;
    for (j = c->begin (); j != eol; j++)
      if (this->eliminated (*j)) break;
    if (j != eol) mark_garbage (c);
  }

  // Assigning units.
  //
  while (!unsat && !units.empty ()) {
    const int unit = units.back (), tmp = val (unit);
    if (!tmp) assign (unit);
    else if (tmp < 0) {
      LOG ("clashing unit %d", unit);
      learn_empty_clause ();
    }
    units.pop_back ();
  }

  // Clean up units stack too.
  //
  dec_bytes (VECTOR_BYTES (units));
  units = vector<int> ();

  inc.elim *= 2;
  lim.elim = stats.conflicts + inc.elim;

  report ('e');
  STOP_AND_SWITCH (elim, simplify, search);
}

};
