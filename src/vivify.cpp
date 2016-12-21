#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"

namespace CaDiCaL {

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

void Internal::vivify () {

  if (!opts.vivify) return;

  SWITCH_AND_START (search, simplify, vivify);

  {
    int remove;
    //opts.log = true;
  }

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
    if (c->redundant) continue;
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

  long tested = 0, subsumed = 0, strengthened = 0;
  vector<int> sorted;

  while (!schedule.empty ()) {
    Clause * c = schedule.back ().clause;
    schedule.pop_back ();
    assert (c->vivify);
    c->vivify = false;
    assert (!c->garbage);
    assert (!c->redundant);
    assert (c->size > 2);
    const const_literal_iterator eoc = c->end ();
    const_literal_iterator j;
    assert (sorted.empty ());
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
	    LOG ("redundant since literal %d already false", lit);
	    remove = lit;
	  } else {
	    assume_decision (-lit);
	    if (propagate ()) continue;
	    LOG ("redundant since conflict produced");
	    backtrack ();
	    conflict = 0;
	    redundant = true;
	  }
	}
	if (level) backtrack ();
	if (redundant) {
	  LOG (c, "redundant asymmetric tautology");
	  mark_garbage (c);
	}
	// TODO 'remove'?
	{
	  int what_if_remove_is_non_zero;
	}
	c->ignore = false;
      }
    }
    sorted.clear ();
  }

  erase_vector (sorted);
  reset_noccs2 ();
  erase_vector (schedule);
  disconnect_watches ();
  connect_watches ();

  VRB ("vivification", stats.vivifications,
    "tested %ld clauses %.02f%% out of scheduled",
    tested, percent (tested, scheduled));
  VRB ("vivification", stats.vivifications,
    "subsumed %ld clauses %.02f%% out of tested",
    subsumed, percent (subsumed, tested));
  VRB ("vivification", stats.vivifications,
    "strengthened %ld clauses %.02f%% out of tested",
    strengthened, percent (strengthened, tested));

  assert (vivifying);
  vivifying = false;

  {
    int remove;
    // opts.log = false;
  }

  report ('v');
  STOP_AND_SWITCH (vivify, simplify, search);
}

};
