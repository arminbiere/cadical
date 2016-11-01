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

inline void Internal::elim (int pivot, vector<int> & work) {
  if (val (pivot)) return;
  assert (!eliminated (pivot));
  vector<Clause*> & ps = occs[pivot];
  vector<Clause*> & ns = occs[-pivot];
  const_clause_iterator i;
  clause_iterator k;
  k = ps.begin ();
  for (i = k; i != ps.end (); i++)
    if ((*k++ = *i)->garbage) k--;
  ps.resize (k - ps.begin ());
  k = ns.begin ();
  for (i = k; i != ns.end (); i++)
    if ((*k++ = *i)->garbage) k--;
  ns.resize (k - ns.begin ());
  long pos = ps.size ();
  long neg = ns.size ();
  if (pos > opts.elimocclim) return;
  if (neg > opts.elimocclim) return;
  if (pos > neg) { swap (pos, neg); swap (ps, ns); pivot = -pivot; }
  long limit = pos + neg, count = 0;
  LOG ("try to eliminate %d with %ld = %ld + %ld occurrences",
    pivot, limit, pos, neg);
  work.clear ();
  bool failed = false;
  for (i = ps.begin (); !failed && !unsat && i != ps.end (); i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    int csize = 0;
    const_literal_iterator end = c->end (), l;
    for (l = c->begin (); l != end; l++) {
      int lit = *l;
      if (lit == pivot) continue;
      int tmp = val (lit);
      if (tmp > 0) break;
      else if (tmp < 0) continue;
      else csize++;
    }
    if (l != end) {
      LOG (c, "skipping satisfied first antecedent");
      mark_garbage (c);
      continue;
    }
    LOG (c, "first actual size %d antecedent", csize + 1);
    const_clause_iterator j;
    for (j = ns.begin (); !failed && !unsat && j != ns.end (); j++) {
      Clause * d = *j;
      if (d->garbage) continue;
      int tautology = 0;
      size_t before = work.size ();
      int dsize = 0, unit = 0;
      end = d->end ();
      for (l = d->begin (); !tautology && l != end; l++) {
	int lit = *l;
	assert (lit != pivot);
	if (lit == -pivot) continue;
	int tmp = val (lit);
	if (tmp > 0) tautology = 2;
	else if (tmp < 0) continue;
	else {
	  tmp = marked (lit);
	  unit = lit;
	  if (tmp > 0) continue;
	  else if (tmp < 0) tautology = 1;
	  else work.push_back (lit), dsize++;
	}
      }
      if (tautology == 2) {
	LOG (d, "skipping satisfied second antecedent");
	work.resize (before);
	continue;
      }
      stats.resolutions++;
      int size = csize + dsize;
      LOG (d, "second actual size %d antecedent", dsize + 1);
      if (!size) {
	LOG ("empty resolvent");
	learn_empty_clause ();
	work.resize (before);
      } else if (tautology == 1) {
	LOG ("tautological resolvent");
	work.resize (before);
      } else if (size == 1 && val (unit) < 0) {
	LOG ("clashing unit %d resolvent", unit);
	learn_empty_clause ();
	work.resize (before);
      } else if (size == 1 && val (unit) > 0) {
	LOG ("ignoring redundant unit resolvent %d", unit);
	work.resize (before);
      } else if (size == 1) {
	LOG ("new unit resolvent %d", unit);
	work.resize (before);
	assign (unit);
      } else if (size > opts.elimclslim) {
	LOG ("non-tautological resolvent of size %d too big", size);
	failed = true;
      } else {
	LOG ("resolvent non-tautological");
	if (++count > limit) { 
	  LOG ("limit %ld non-tautological resolvents exhausted", limit);
	  failed = true;
	} else {
	  end = c->end ();
	  for (l = c->begin (); l != end; l++)
	    if (*l != pivot && !val (*l)) work.push_back (*l);
	  work.push_back (0);
	}
      }
    }
    unmark (c);
  }
  if (unsat) { LOG ("elimination produced empty clause"); return ;}
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
    mark_garbage (*i);
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
  if (lim.fixed_at_last_collect < stats.fixed) garbage_collection ();

  // Allocate schedule and occurrence lists.
  //
  vector<int> schedule, work;
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
  for (k = schedule.begin (); !unsat && k != eos; k++)
    elim (*k, work);				// TODO garbage collection!

  inc_bytes (VECTOR_BYTES (work));

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

  // Collect everything.  
  //
  garbage_collection ();

  inc.elim *= 2;
  lim.elim = stats.conflicts + inc.elim;

  report ('e');
  STOP_AND_SWITCH (elim, simplify, search);
}

};
