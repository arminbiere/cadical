#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"

namespace CaDiCaL {

// Vivification is a special case of asymmetric tautology elimination.  It
// strengthens and removes irredundant clauses proven redundant through unit
// propagation.  The original algorithm is due to a paper by Piette, Hamadi
// and Sais published at ECAI'08.  This is an inprocessing version, e.g.,
// does not necessarily run-to-completion.  It only learns units in case of
// conflict and uses a new heuristic for selecting clauses to vivify.

/*------------------------------------------------------------------------*/

struct ClauseScore {
  Clause * clause;
  long score;
  ClauseScore (Clause * c) : clause (c), score (0) { }
};

struct less_clause_score {
  bool operator () (const ClauseScore & a, const ClauseScore & b) const {
    return a.score < b.score;
  }
};

struct less_negated_noccs2 {
  Internal * internal;
  less_negated_noccs2 (Internal * i) : internal (i) { }
  bool operator () (int a, int b) {
    long u = internal->noccs2 (-a), v = internal->noccs2 (-b);
    if (u < v) return true;
    if (u > v) return false;
    int i = abs (a), j = abs (b);
    if (i < j) return true;
    if (i > j) return false;
    return a < b;
  }
};

/*------------------------------------------------------------------------*/

// This a specialized instance of 'analyze', which only concludes with a
// learned unit (still a first UIP clause though), if one exists.  If the
// learned clause would have a literal on a different non-zero level, we do
// not learn anything.  The learned unit is returned.

int Internal::vivify_analyze () {

  assert (level);
  assert (!unsat);
  assert (conflict);
  assert (analyzed.empty ());

  START (analyze);

  Clause * reason = conflict;
  LOG (reason, "vivification analyzing conflict");
  int open = 0, uip = 0;
  const_int_iterator i = trail.end ();
  for (;;) {
    const const_literal_iterator end = reason->end ();
    const_literal_iterator j = reason->begin ();
    while (uip && j != end) {
      const int other = *j++;
      if (other == uip) continue;
      Flags & f = flags (other);
      if (f.seen) continue;
      Var & v = var (other);
      if (!v.level) continue;
      if (v.level == level) {
	analyzed.push_back (other);
	f.seen = true;
	open++;
      } else uip = 0;		// and abort
    }
    if (!uip) break;
    while (!flags (uip = *--i).seen)
      ;
    if (!--open) break;
    reason = var (uip).reason;
    LOG (reason, "vivification analyzing %d reason", uip);
  }

  backtrack ();
  clear_seen ();
  conflict = 0;

	  COVER (uip);

  if (uip) {
    LOG ("vivification first UIP %d", uip);
    assert (!val (uip));
    assign_unit (-uip);
    if (!propagate ()) learn_empty_clause ();
  } else LOG ("no unit learned");

  STOP (analyze);

  return -uip;
}

/*------------------------------------------------------------------------*/

void Internal::vivify () {

  assert (opts.vivify);

  SWITCH_AND_START (search, simplify, vivify);

  assert (!vivifying);
  vivifying = true;

  stats.vivifications++;
  if (level) backtrack ();

  vector<ClauseScore> schedule;

  const const_clause_iterator end = clauses.end ();
  const_clause_iterator i;

  bool no_new_units = (lim.fixed_at_last_collect >= stats.fixed);

  for (int round = 0; schedule.empty () && round <= 1; round++) {
    for (i = clauses.begin (); i != end; i++) {
      Clause * c = *i;
      if (c->garbage) continue;
      if (c->redundant) continue;
      if (c->size == 2) continue;
      int fixed;
      if (no_new_units || round) fixed = 0;
      else fixed = clause_contains_fixed_literal (c);
      if (fixed > 0) mark_garbage (c);
      else {
	if (fixed < 0) remove_falsified_literals (c);
	if (c->size == 2) continue;
	if (!round && !c->vivify) continue;
	schedule.push_back (c);
	c->vivify = true;
      }
    }
  }

  shrink_vector (schedule);

  init_noccs2 ();

  for (i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    const const_literal_iterator eoc = c->end ();
    const_literal_iterator j;
    for (j = c->begin (); j != eoc; j++)
      noccs2 (*j)++;
  }

  const vector<ClauseScore>::const_iterator eos = schedule.end ();
  vector<ClauseScore>::iterator k;

  for (k = schedule.begin (); k != eos; k++) {
    ClauseScore & cs = *k;
    const const_literal_iterator eoc = cs.clause->end ();
    const_literal_iterator j;
    long score = 0;
    for (j = cs.clause->begin (); j != eoc; j++)
      score += noccs2 (-*j);
    cs.score = score;
  }

  stable_sort (schedule.begin (), schedule.end (), less_clause_score ());

  long scheduled = schedule.size ();
  VRB ("vivification", stats.vivifications,
    "scheduled irredundant %ld clauses to be vivified %.0f%%",
    scheduled, percent (scheduled, stats.irredundant));

  flush_redundant_watches ();

  long checked = 0, subsumed = 0, strengthened = 0, units = 0;
  vector<int> sorted;

  // Limit the number of propagations during vivification as in 'probe'.
  //
  long delta = opts.vivifyreleff * stats.propagations.search;
  if (delta < opts.vivifymineff) delta = opts.vivifymineff;
  if (delta > opts.vivifymaxeff) delta = opts.vivifymaxeff;
  long limit = stats.propagations.vivify + delta;

  while (!unsat &&
         !schedule.empty () &&
         stats.propagations.vivify < limit) {

    Clause * c = schedule.back ().clause;
    schedule.pop_back ();
    assert (c->vivify);
    c->vivify = false;

    assert (!c->garbage);
    assert (!c->redundant);
    assert (c->size > 2);
    assert (sorted.empty ());
    assert (!level);

    const const_literal_iterator eoc = c->end ();
    const_literal_iterator j;
    bool satisfied = false;

    for (j = c->begin (); !satisfied && j != eoc; j++) {
      const int lit = *j, tmp = val (lit);
      if (tmp > 0) satisfied = true;
      else if (!tmp) sorted.push_back (lit);
    }

    if (satisfied) mark_garbage (c);
    else {
      assert (sorted.size () >= 2);
      if (sorted.size () > 2) {
	checked++;
	LOG (c, "vivification checking");
	sort (sorted.begin (), sorted.end (), less_negated_noccs2 (this));
	c->ignore = true;
	bool redundant = false;
	int remove = 0;
	while (!redundant && !remove && !sorted.empty ()) {
	  const int lit = sorted.back (), tmp = val (lit);
	  sorted.pop_back ();
	  if (tmp > 0) {
	    LOG ("redundant since literal %d already true", lit);
	    redundant = true;
	  } else if (tmp < 0) {
	    LOG ("removing literal %d which is already false", lit);
	    remove = lit;
	  } else {
	    assume_decision (-lit);
	    if (propagate ()) continue;
	    LOG ("redundant since conflict produced");
	    if (vivify_analyze ()) units++;
	    redundant = true;
	  }
	}
	if (redundant) {
REDUNDANT:
	  if (level) backtrack ();
	  LOG (c, "redundant asymmetric tautology");
	  mark_garbage (c);
	  subsumed++;
	} else if (remove) {
	  strengthened++;
	  assert (level);
	  assert (clause.empty ());
	  for (j = c->begin (); j != eoc; j++) {
	    const int other = *j, tmp = val (other);
	    Var & v = var (other);
	    if (tmp > 0) {
	      clause.clear ();
	      goto REDUNDANT;
	    }
	    if (tmp < 0 && !v.level) continue;
	    if (tmp < 0 && v.level && v.reason) {
	      assert (v.level);
	      assert (v.reason);
	      LOG ("flushing literal %d", other);
	      mark_removed (other);
	    } else clause.push_back (other);
	  }
	  assert (!clause.empty ());
	  backtrack ();
	  if (clause.size () == 1) {
	    const int unit = clause[0];
	    LOG (c, "vivification shrunken to unit %d", unit);
	    assert (!val (unit));
	    assign_unit (unit);
	    units++;
	    if (!propagate ()) learn_empty_clause ();
	  } else {
#ifdef LOGGING
	    Clause * d = 
#endif
	    new_clause_as (c);
	    LOG (c, "before vivification");
	    LOG (d, "after vivification");
	  }
	  clause.clear ();
	  mark_garbage (c);
	} else backtrack ();
	c->ignore = false;
      }
    }
    sorted.clear ();
  }

  if (!unsat) {
    erase_vector (sorted);
    reset_noccs2 ();
    erase_vector (schedule);
    disconnect_watches ();
    connect_watches ();
  }

  VRB ("vivification", stats.vivifications,
    "checked %ld clauses %.02f%% out of scheduled",
    checked, percent (checked, scheduled));
  VRB ("vivification", stats.vivifications,
    "found %ld units %.02f%% out of checked",
    units, percent (units, checked));
  VRB ("vivification", stats.vivifications,
    "subsumed %ld clauses %.02f%% out of checked",
    subsumed, percent (subsumed, checked));
  VRB ("vivification", stats.vivifications,
    "strengthened %ld clauses %.02f%% out of checked",
    strengthened, percent (strengthened, checked));

  stats.vivifychecks += checked;
  stats.vivifysubs += subsumed;
  stats.vivifystrs += strengthened;
  stats.vivifyunits += units;

  stats.subsumed += subsumed;
  stats.strengthened += strengthened;

  assert (vivifying);
  vivifying = false;

  report ('v');
  STOP_AND_SWITCH (vivify, simplify, search);
}

};
