#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Vivification is a special case of asymmetric tautology elimination and
// asymmetric literal elimination.  It strengthens and removes irredundant
// clauses proven redundant through unit propagation.  The original
// algorithm is due to a paper by Piette, Hamadi and Sais published at
// ECAI'08.  We have an inprocessing version, e.g., it does not necessarily
// run-to-completion.  Our version does not perform any conflict analysis
// and uses a new heuristic for selecting clauses to vivify. The idea is to
// focus on long clauses with many occurrences of its literals in other
// clauses first.  This both complements nicely our implementation of
// subsume, which is bounded, e.g., subsumption attempts are skipped for
// very long clauses with literals with many occurrences and also is
// stronger in the sence that it enables to remove more clauses.

/*------------------------------------------------------------------------*/

// Used to sort (schedule) candidate clauses.

struct ClauseScore {

  Clause * clause;
  double score;			// sum number of occurrences of literals

  ClauseScore (Clause * c) : clause (c), score (0) { }
};

struct less_clause_score {
  bool operator () (const ClauseScore & a, const ClauseScore & b) const {
    return a.score < b.score;
  }
};

// Check whether literal occurs less often.

struct vivify_less_noccs {

  Internal * internal;

  vivify_less_noccs (Internal * i) : internal (i) { }

  bool operator () (int a, int b) {

    bool s = internal->val (a) > 0;
    bool t = internal->val (b) > 0;
    
    if (!s & t) return true;
    if (s & !t) return false;

    if (s & t) return internal->var (a).level > internal->var (b).level;

    long n = internal->noccs (a);
    long m = internal->noccs (a);
    if (n < m) return true;
    if (n > m) return false;

    assert (a != b), assert (a != -b);

    return abs (a) > abs (b);
  }
};

/*------------------------------------------------------------------------*/

void Internal::vivify () {

  if (unsat) return;

  assert (opts.vivify);
  SWITCH_AND_START (search, simplify, vivify);

  assert (!vivifying);
  vivifying = true;

  stats.vivifications++;
  if (level) backtrack ();

  // Refill the schedule every time.  Unchecked clauses are 'saved' by
  // setting their 'vivify' bit, such that they can be tried next time.
  //
  vector<ClauseScore> schedule;

  const const_clause_iterator end = clauses.end ();
  const_clause_iterator i;

  // After an arithmetic increasing number of calls to 'vivify' we
  // reschedule all clauses, instead of only those not tried before.  Then
  // this limit is increased by one. The argument is that we should focus on
  // clauses with many occurrences of their literals (also long clauses),
  // but in the limit eventually still should vivify all clauses.
  //
  bool reschedule_all;
  if (opts.vivifyreschedule) {
    reschedule_all = !lim.vivify_wait_reschedule;
    if (reschedule_all) {
      VRB ("vivify", stats.vivifications,
	"forced to reschedule all clauses");
      lim.vivify_wait_reschedule = ++inc.vivify_wait_reschedule;
    } else lim.vivify_wait_reschedule--;
  } else reschedule_all = false;

  // In the first round check whether there are still clauses left, which
  // are scheduled but have not been vivified yet.  In the second round,
  // if no such clauses are found in the first round, all clauses are
  // selected.  This second round is also performed if rescheduling is
  // forced because 'reschedule_all' is  true.
  //
  for (int round = 0; schedule.empty () && round <= 1; round++) {
    for (i = clauses.begin (); i != end; i++) {
      Clause * c = *i;
      if (c->garbage) continue;
      if (c->redundant) continue;
      if (c->size == 2) continue;       // see also [NO-BINARY] below
      if (!reschedule_all && !round && !c->vivify) continue;
      schedule.push_back (c);
      c->vivify = true;
    }
  }
  shrink_vector (schedule);

  // Count the number of occurrences of literals in all irredundant clauses,
  // particularly the irredundant binary clauses, responsible for most of
  // the propagation usually.
  //
  init_noccs ();

  for (i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    if (c->redundant) continue;

    // Compute score as 'pow (2, -c->size)' without 'math.h' (it actually
    // could be faster even, since second argument is always an integer).
    //
    // This is the same score as the Jeroslow-Wang heuristic would give.
    //
    // There is no point in pre-computing this since the following loop
    // updating the score of all literals in the clause shoule be way more
    // expensive since it is linear in the size of the clause (not
    // logarithmic) and has to access much more memory.
    //
    double base = 0.5, score = 0.25;
    for (int n = c->size - 2; n; n >>= 1) {
      if (n & 1) score *= base;
      base *= base;
    }

    const const_literal_iterator eoc = c->end ();
    const_literal_iterator j;
    for (j = c->begin (); j != eoc; j++)
      noccs (*j) += score;
  }

  // Then update the score of the candidate clauses by adding up the score.
  //
  const vector<ClauseScore>::const_iterator eos = schedule.end ();
  vector<ClauseScore>::iterator k;

  for (k = schedule.begin (); k != eos; k++) {
    ClauseScore & cs = *k;
    const const_literal_iterator eoc = cs.clause->end ();
    const_literal_iterator j;
    long score = 0;
    for (j = cs.clause->begin (); j != eoc; j++)
      score += noccs (*j);
    cs.score = score;
  }

  // Now sort candidates, with best clause (many occurrences) last.
  //
  stable_sort (schedule.begin (), schedule.end (), less_clause_score ());

#ifndef QUIET
  long scheduled = schedule.size ();
  VRB ("vivify", stats.vivifications,
    "scheduled %ld clauses to be vivified %.0f%%",
    scheduled, percent (scheduled, stats.irredundant));
#endif

  // We need to make sure to propagate only over irredundant clauses.
  //
  flush_redundant_watches ();
  size_t old_propagated = propagated;   // see [RE-PROPAGATE] below.

  // Counters, for what happened.
  //
  long checked = 0, subsumed = 0, strengthened = 0, units = 0;

  // Temporarily save and sort the candidate clause literals here.
  //
  vector<int> sorted;

  // Limit the number of propagations during vivification as in 'probe'.
  //
  long delta = stats.propagations.search;
  delta -= lim.search_propagations.vivify;
  delta *= opts.vivifyreleff;
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
    assert (c->size > 2);               // see [NO-BINARY] above

    // First check whether it is already satisfied and at the same time copy
    // the literals of the clause to the 'sorted' stack.
    //
    const const_literal_iterator eoc = c->end ();
    const_literal_iterator j;
    bool satisfied = false;

    sorted.clear ();

    for (j = c->begin (); !satisfied && j != eoc; j++) {
      const int lit = *j, tmp = fixed (lit);
      if (tmp > 0) satisfied = true;
      else if (!tmp) sorted.push_back (lit);
    }

    if (satisfied) { mark_garbage (c); continue; }

    // The actual vivification checking is performed here, by assuming the
    // negation of each of the remaining literals of the clause in turn and
    // propagating it.  If a conflict occurs or another literal in the
    // clause becomes assigned during propagation, we can stop.
    //
    LOG (c, "vivification checking");
    checked++;

    // Sort the literals of the candidate with respect to the largest number
    // of occurrences.  The idea is that more occurrences leads to more
    // propagations and thus potentially higher earlier effect.
    //
    sort (sorted.begin (), sorted.end (), vivify_less_noccs (this));

    // We are trying to reuse the decisions, the trail and the propagations
    // of the previous vivification candidate.  The 'sorted' stack contains
    // satisfied literals at the end in decreasing decision level order. As
    // long those match decisions on trail we just reuse them.
    //
    int l = 1;
    while (!sorted.empty () && l <= level) {
      const int decision = control[l].decision;
      const int lit = sorted.back ();
      if (-lit == decision) {
	LOG ("reusing decision %d at decision level %d", decision, l);
	sorted.pop_back ();
	l++;
      } else { 
	LOG ("literal %d does not match decision %d at decision level %d",
	  lit, decision, l);
	backtrack (l-1);
	break;
      }
    }

    if (level) LOG ("reused %d decision levels", level);
    else LOG ("no decision level reused");

    // TODO add statistics on reusing decision levels.

    // Make sure to ignore this clause during propagation.  This is not that
    // easy for binary clauses [NO-BINARY], e.g., ignoring binary clauses,
    // without changing 'propagate' and actually we also do not want to
    // remove binary clauses which are subsumed.  Those are hyper binary
    // resolvents and should be kept as learned clauses instead unless they
    // are transitive in the binary implication graph, which in turn is
    // detected during transitive reduction in 'transred'.
    //
    c->ignore = true;           // see also [NO-BINARY] above

    bool redundant = false;     // determined to be redundant / subsumed
    int remove = 0;             // at least literal 'remove' can be removed

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
	assert (level > 0);
	backtrack (level - 1);
        conflict = 0;
      }
    }

    if (redundant) {
REDUNDANT:
      subsumed++;
      LOG (c, "redundant asymmetric tautology");
      mark_garbage (c);
    } else if (remove) {
      assert (level);
      assert (clause.empty ());
#ifndef NDEBUG
      bool found = false;
#endif
      // There might be other literals implied to false (or even root level
      // falsified).  Those should be removed in addition to 'remove'.  It
      // might further be possible that a latter to be assumed literal is
      // already forced to true in which case the clause is actually
      // redundant (we solved this by bad style 'goto' programming).
      //
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

      // Assume remaining literals and propagate them to see whether this
      // clause is actually redundant and does not have to be strengthened.

      if (!sorted.empty ()) {

	do {
	  const int lit = sorted.back (), tmp = val (lit);
	  sorted.pop_back ();
	  if (tmp < 0) continue;
	  if (tmp > 0) {
	    LOG ("redundant since literal %d already true", lit);
	    redundant = true;
	  } else {
	    assume_decision (-lit);
	    redundant = !propagate ();
	  }
	} while (!redundant && !sorted.empty ());

	if (redundant) {
	  if (conflict) {
	    assert (level > 0);
	    backtrack (level - 1);
	    conflict = 0;
	  }
          LOG ("redundant since propagating rest produces conflict");
	  clause.clear ();
	  goto REDUNDANT;
	}

	LOG ("propagating remaining negated literals without conflict");
      }

      strengthened++; // only now because of 'goto REDUNDANT' above (twice)

      assert (!clause.empty ());

      if (clause.size () == 1) {
	backtrack (0);
        const int unit = clause[0];
        LOG (c, "vivification shrunken to unit %d", unit);
        assert (!val (unit));
        assign_unit (unit);
        units++;
        bool ok = propagate ();
        if (!ok) learn_empty_clause ();
      } else {
	assert (clause.size () > 1);
	int lit0 = clause[0];
	int lit1 = clause[1];
	int val0 = val (lit0);
	int val1 = val (lit1);
	int trail0 = var (lit0).level;
	int trail1 = var (lit1).level;
	int level0 = var (lit0).level;
	int level1 = var (lit1).level;
	int l;
	if (val0 < 0 && val1 < 0) l = min (level0, level1) - 1;
	else if (val0 < 0 && (!val1 || trail1 > trail0)) l = level0 - 1;
	else if (val1 < 0 && (!val0 || trail0 > trail1)) l = level1 - 1;
	else l = level;
	if (l < level) backtrack (l);
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
    c->ignore = false;
  }

  if (level) backtrack ();

  if (!unsat) {

    erase_vector (sorted);
    reset_noccs ();
    erase_vector (schedule);
    disconnect_watches ();
    connect_watches ();

    // [RE-PROPAGATE] Since redundant clause were disconnected during
    // propagating vivified units above, we have propagate all those fixed
    // literals again after connecting the redundant clauses back.
    // Otherwise, the invariants for watching and blocking literals break.
    //
    if (old_propagated < propagated) {
      propagated = old_propagated;
      if (!propagate ()) {
        LOG ("propagating vivified units leads to conflict");
        learn_empty_clause ();
      }
    }
  }

  VRB ("vivify", stats.vivifications,
    "checked %ld clauses %.02f%% out of scheduled",
    checked, percent (checked, scheduled));
  if (units)
  VRB ("vivify", stats.vivifications,
    "found %ld units %.02f%% out of checked",
    units, percent (units, checked));
  VRB ("vivify", stats.vivifications,
    "subsumed %ld clauses %.02f%% out of checked",
    subsumed, percent (subsumed, checked));
  VRB ("vivify", stats.vivifications,
    "strengthened %ld clauses %.02f%% out of checked",
    strengthened, percent (strengthened, checked));

  stats.vivifychecks += checked;
  stats.vivifysubs += subsumed;
  stats.vivifystrs += strengthened;
  stats.vivifyunits += units;

  stats.subsumed += subsumed;
  stats.strengthened += strengthened;

  lim.search_propagations.vivify = stats.propagations.search;

  assert (vivifying);
  vivifying = false;

  report ('v');
  STOP_AND_SWITCH (vivify, simplify, search);
}

};
