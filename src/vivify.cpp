#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"

namespace CaDiCaL {

// Vivification is a special case of asymmetric tautology elimination.  It
// strengthens and removes irredundant clauses proven redundant through unit
// propagation.  The original algorithm is due to a paper by Piette, Hamadi
// published at ECAI'08.  We have an inprocessing version, e.g., it does not
// necessarily run-to-completion.  It does no conflict analysis and uses a
// new heuristic for selecting clauses to vivify.

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
  bool reschedule_all = !lim.vivifywaitreset;
  if (reschedule_all) lim.vivifywaitreset = ++inc.vivifywaitreset;
  else lim.vivifywaitreset--;

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
	if (!reschedule_all && !round && !c->vivify) continue;
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

    // Next candidate clause to vivify.
    //
    Clause * c = schedule.back ().clause;
    schedule.pop_back ();
    assert (c->vivify);
    c->vivify = false;

    assert (!c->garbage);
    assert (!c->redundant);
    assert (c->size > 2);
    assert (!level);

    // First check whether it is already satisfied.
    //
    const const_literal_iterator eoc = c->end ();
    const_literal_iterator j;
    bool satisfied = false;

    sorted.clear ();

    for (j = c->begin (); !satisfied && j != eoc; j++) {
      const int lit = *j, tmp = val (lit);
      if (tmp > 0) satisfied = true;
      else if (!tmp) sorted.push_back (lit);
    }

    if (satisfied) { mark_garbage (c); continue; }

    // if (sorted.size () == 2) continue;

    // The actual vivification checking is performed here, by assuming the
    // negation of each of the remaining literals of the clause in turn and
    // propagating it.  If a conflict occurs or another literal in the
    // clause becomes assigned during propagation, we can stop.
    //
    LOG (c, "vivification checking");
    checked++;

    // Sort the literals of the candidate with respect to the largest number
    // of negative occurrences.  The idea is that more negative occurrences
    // lead to more propagations and thus potentially higher earlier effect.
    //
    sort (sorted.begin (), sorted.end (), less_negated_noccs2 (this));
   
    // Make sure to ignore this clause during propagation.  This is not that
    // easy for binary clauses, e.g., ignoring binary clauses, without
    // changing 'propagate' and actually we also do not want to remove
    // binary clauses which are subsumed.  Those are hyper binary
    // resolvents and should be kept as learned clauses instead (TODO).
    //
    c->ignore = true;

    bool redundant = false;	// determined to be redundant / subsumed
    int remove = 0;		// at least literal 'remove' can be removed

    while (!redundant && !remove && !sorted.empty ()) {
      const int lit = sorted.back (), tmp = val (lit);
      sorted.pop_back ();
      if (tmp > 0) {
	LOG ("redundant since literal %d already true", lit);
	redundant = true;
      } else if (tmp < 0) {
	LOG ("removing at least literal %d which is already false", lit);
	remove = lit;
      } else {
	assume_decision (-lit);
	if (propagate ()) continue;
	LOG ("redundant since propagation produced conflict");
	redundant = true;
	conflict = 0;
      }
    }

    if (redundant) {
REDUNDANT:
      LOG (c, "redundant asymmetric tautology");
      mark_garbage (c);
      subsumed++;
    } else if (remove) {
      strengthened++;
      assert (level);
      assert (clause.empty ());
#ifndef NDEBUG
      bool found = false;
#endif
      for (j = c->begin (); j != eoc; j++) {
	const int other = *j, tmp = val (other);
	Var & v = var (other);
	if (tmp > 0) {
	  LOG ("redundant since literal %d already true", other);
	  clause.clear ();
	  goto REDUNDANT;
	}
	if (tmp < 0 && !v.level) continue;
	if (tmp < 0 && v.level && v.reason) {
	  assert (v.level);
	  assert (v.reason);
	  LOG ("flushing literal %d", other);
	  mark_removed (other);
#ifndef NDEBUG
	  if (other == remove) found = true;
#endif
	} else clause.push_back (other);
      }
      assert (found);
      assert (!clause.empty ());
      backtrack ();
      if (clause.size () == 1) {
	const int unit = clause[0];
	LOG (c, "vivification shrunken to unit %d", unit);
	assert (!val (unit));
	assign_unit (unit);
	units++;
	bool ok = propagate ();
	if (!ok) learn_empty_clause ();
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
    }
    if (level) backtrack ();
    c->ignore = false;
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
