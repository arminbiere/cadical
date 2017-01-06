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

// Check whether literal occurs less often.

struct vivify_more_noccs {

  Internal * internal;

  vivify_more_noccs (Internal * i) : internal (i) { }

  bool operator () (int a, int b) {
    long n = internal->noccs (a);
    long m = internal->noccs (b);
    if (n > n) return true;
    if (n < m) return false;
    if (a == -b) return a > 0;
    return abs (a) < abs (b);
  }
};

// Sort candidate clauses by the number of occurrences of their literals,
// with clauses to be vivified first last.   We assume that clauses are
// sorted w.r.t. more occurring literals first (with 'vivify_more_noccs').

struct vivify_less_clause {

  Internal * internal;

  vivify_less_clause (Internal * i) : internal (i) { }

  bool operator () (Clause * a, Clause * b) const {
    assert (!a->redundant), assert (!b->redundant);
    const const_literal_iterator eoa = a->end (), eob = b->end ();
    const_literal_iterator i = a->begin (), j = b->begin ();
    for (i = a->begin (), j = b->begin (); i != eoa && j != eob; i++, j++)
      if (*i != *j) return vivify_more_noccs (internal) (*j, *i);
    if (i == eoa) {
      if (!b->garbage) {
	LOG (b, "vivification sorting finds subsumed");
	internal->mark_garbage (b);
      }
      return true;
    } else {
      assert (j == eob);
      if (!a->garbage) {
	LOG (a, "vivification sorting finds subsumed");
	internal->mark_garbage (a);
      }
      return false;
    }
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

  // Disconnect all watches since we sort literals in irredundant clauses.
  //
  disconnect_watches ();

  // Count the number of occurrences of literals in all irredundant clauses,
  // particularly the irredundant binary clauses, usually responsible for
  // most of the propagations.
  //
  init_noccs ();

  const const_clause_iterator end = clauses.end ();
  const_clause_iterator i;

  for (i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (c->garbage || c->redundant) continue;
    const const_literal_iterator eoc = c->end ();
    const_literal_iterator j;
    for (j = c->begin (); j != eoc; j++)
      noccs (*j)++;
  }

  // After an arithmetic increasing number of calls to 'vivify' reschedule
  // all clauses, instead of only those not tried before.  Then this limit
  // is increased by one. The argument is that we should focus on clauses
  // with many occurrences of their literals (also long clauses), but in the
  // limit eventually still should vivify all clauses.
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

  // Refill the schedule every time.  Unchecked clauses are 'saved' by
  // setting their 'vivify' bit, such that they can be tried next time.
  //
  vector<Clause*> schedule;

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
      sort (c->begin (), c->end (), vivify_more_noccs (this));
      schedule.push_back (c);
      c->vivify = true;
    }
  }
  shrink_vector (schedule);

  // Now sort candidates, with first candidate clause (many occurrences) last.
  //
  stable_sort (schedule.begin (), schedule.end (), vivify_less_clause (this));

#ifndef QUIET
  long scheduled = schedule.size ();
  VRB ("vivify", stats.vivifications,
    "scheduled %ld clauses to be vivified %.0f%%",
    scheduled, percent (scheduled, stats.irredundant));
#endif

  // We need to make sure to propagate units also over redundant clauses.
  //
  size_t old_propagated = propagated;   // see [RE-PROPAGATE] below.

  // Counters, for what happened.
  //
  long checked = 0, subsumed = 0, strengthened = 0, units = 0;

  // Limit the number of propagations during vivification as in 'probe'.
  //
  long delta = stats.propagations.search;
  delta -= lim.search_propagations.vivify;
  delta *= opts.vivifyreleff;
  if (delta < opts.vivifymineff) delta = opts.vivifymineff;
  if (delta > opts.vivifymaxeff) delta = opts.vivifymaxeff;
  long limit = stats.propagations.vivify + delta;

  connect_watches (true);		// watch only irredundant clauses

  while (!unsat &&
         !schedule.empty () &&
         stats.propagations.vivify < limit) {

    // Next candidate clause to vivify.
    //
    Clause * c = schedule.back ();
    schedule.pop_back ();
    assert (c->vivify);
    c->vivify = false;

    assert (!c->garbage);
    assert (!c->redundant);
    assert (c->size > 2);               // see [NO-BINARY] above

    // First check whether the candidate clause is already satisfied.
    //
    const const_literal_iterator eoc = c->end ();
    const_literal_iterator j;
    bool satisfied = false;

    for (j = c->begin (); !satisfied && j != eoc; j++)
      satisfied = (fixed (*j) > 0);

    if (satisfied) { 
      LOG (c, "satisfied by propagated unit");
      mark_garbage (c);
      continue;
    }

    // The actual vivification checking is performed here, by assuming the
    // negation of each of the remaining literals of the clause in turn and
    // propagating it.  If a conflict occurs or another literal in the
    // clause becomes assigned during propagation, we can stop.
    //
    LOG (c, "vivification checking");
    checked++;

    // We are trying to reuse decisions, the trail and the propagations of
    // the previous vivification candidate.  As long the literals of the
    // clause match decisions on the trail we just reuse them.
    //
    int l = 1;
    for (j = c->begin (); j != eoc && l <= level; j++) {
      const int lit = *j;
      if (fixed (lit)) continue;
      const int decision = control[l].decision;
      if (-lit == decision) {
	LOG ("reusing decision %d at decision level %d", decision, l);
	stats.vivifyreused++;
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

    for (j = c->begin (); !redundant && !remove && j != eoc; j++) {
      const int lit = *j, tmp = val (lit);
      if (tmp) {
	const Var & v = var (lit);
	if (!v.level) { LOG ("skipping fixed %d", lit); continue; }
	if (!v.reason) { LOG ("skipping decision %d", lit); continue; }
	if (tmp > 0) {
	  LOG ("redundant since literal %d already true", lit);
	  redundant = true;
	} else {
	  assert (tmp < 0);
	  LOG ("removing at least literal %d which is already false", lit);
	  remove = lit;
	}
      } else {
	stats.vivifydecs++;
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
      while (j != eoc) {
        const int other = *j++, tmp = val (other);
        Var & v = var (other);
        if (tmp > 0) {
	  assert (v.level), assert (v.reason);
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

      strengthened++; // only now because of 'goto REDUNDANT' above

      backtrack ();

      assert (!clause.empty ());

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
    c->ignore = false;
  }

  if (level) backtrack ();

  if (!unsat) {

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
