#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Vivification is a special case of asymmetric tautology elimination and
// asymmetric literal elimination.  It strengthens and removes irredundant
// clauses proven redundant through unit propagation.
//
// The original algorithm is due to a paper by Piette, Hamadi and Sais
// published at ECAI'08.  We have an inprocessing version, e.g., it does not
// necessarily run-to-completion.  Our version also performs conflict
// analysis and uses a new heuristic for selecting clauses to vivify. The
// idea is to focus on long clauses with many occurrences of its literals in
// other clauses first.  This both complements nicely our implementation of
// subsume, which is bounded, e.g., subsumption attempts are skipped for
// very long clauses with literals with many occurrences and also is
// stronger in the sense that it enables to remove more clauses.
//
// While first focusing on irredundant clause we then added a separate phase
// upfront which focuses on strengthening also redundant clauses in spirit
// of the ideas presented in the IJCAI'17 paper by M. Luo, C.-M. Li, F.
// Xiao, F. Manya, and Z. Lu.

/*------------------------------------------------------------------------*/

// Check whether a literal occurs less often.  In the implementation below
// (search for 'long score = ...' or '@4') we actually compute a weighted
// occurrence count similar to the Jeroslow Wang heuristic.

struct vivify_more_noccs {

  Internal * internal;

  vivify_more_noccs (Internal * i) : internal (i) { }

  bool operator () (int a, int b) {
    long n = internal->noccs (a);
    long m = internal->noccs (b);
    if (n > m) return true;	// larger occurrences / score first
    if (n < m) return false;	// smaller occurrences / score last
    if (a == -b) return a > 0;	// positive literal first
    return abs (a) < abs (b);	// smaller index first
  }
};

// Sort candidate clauses by the number of occurrences (actually by their
// score) of their literals, with clauses to be vivified first last.   We
// assume that clauses are sorted w.r.t. more occurring (higher score)
// literals first (with respect to 'vivify_more_noccs').
//
// For example if there are the following (long irredundant) clauses
//
//   1 -3 -4      (A)
//  -1 -2  3 4    (B)
//   2 -3  4      (C)
//
// then we have the following literal scores using Jeroslow Wang scores and
// normalizing it with 2^12 (which is the same as 1<<12):
//
//  nocc ( 1) = 2^12 * (2^-3       ) =  512  3.
//  nocc (-1) = 2^12 * (2^-4       ) =  256  6.
//  nocc ( 2) = 2^12 * (2^-3       ) =  512  4.
//  nocc (-2) = 2^12 * (2^-4       ) =  256  7.			@1
//  nocc ( 3) = 2^12 * (2^-4       ) =  256  8.
//  nocc (-3) = 2^12 * (2^-3 + 2^-3) = 1024  1.
//  nocc ( 4) = 2^12 * (2^-3 + 2^-4) =  768  2.
//  nocc (-4) = 2^12 * (2^-3       ) =  512  5.
//
// which gives the following literal order (according to 'vivify_more_noccs')
//
//  -3, 4, 1, 2, -4, -1, -2, 3
//
// Then sorting the literals in each clause gives
//
//  -3  1 -4     (A')
//   4 -1 -2  3  (B')						@2
//  -3  4  2     (C')
//
// and finally sorting those clauses lexicographically w.r.t. scores is
//
//  -3  4  2     (C')
//  -3  1 -4     (A')						@3
//   4 -1 -2  3  (B')
//
// This order is defined by the following comparison 'vivify_less_clause'.

struct vivify_less_clause {

  Internal * internal;
  bool redundant;

  vivify_less_clause (Internal * i, bool r) :
    internal (i), redundant (r) { }

  bool operator () (Clause * a, Clause * b) const {

    assert (redundant || !a->redundant);
    assert (redundant || !b->redundant);

    if (!a->redundant && b->redundant) return true;
    if (a->redundant && !b->redundant) return false;

    const const_literal_iterator eoa = a->end (), eob = b->end ();
    const_literal_iterator i, j;

    for (i = a->begin (), j = b->begin (); i != eoa && j != eob; i++, j++)
      if (*i != *j) return vivify_more_noccs (internal) (*j, *i);

    return i == eoa;
  }
};

/*------------------------------------------------------------------------*/

// On-the-fly subsumption during sorting in 'vivify_less_clause' above
// turned out to be trouble some for identical clauses.  This is the single
// point where 'vivify_less_clause' is not asymmetric and thus requires
// 'stable' sorting for determinism.  It can also not be made 'complete'
// on-the-fly and thus after sorting the schedule we go over it in a linear
// scan again and remove subsumed clauses.

void Internal::flush_vivification_schedule (
  vector<Clause*> & schedule,
  long & subsumed)
{
  const const_clause_iterator end = schedule.end ();
  clause_iterator j = schedule.begin ();
  const_clause_iterator i;
  Clause * prev = 0;
  for (i = j; i != end; i++) {
    Clause * c = *j++ = *i;
    if (!prev || c->size < prev->size) { prev = c; continue; }
    const const_literal_iterator eop = prev->end ();
    const_literal_iterator k, l;
    for (k = prev->begin (), l = c->begin (); k != eop; k++, l++)
      if (*k != *l) break;
    if (k == eop) {
      LOG (c, "found subsumed");
      LOG (prev, "subsuming");
      assert (!c->garbage);
      assert (!prev->garbage);
      assert (c->redundant || !prev->redundant);
      mark_garbage (c);
      subsumed++;
      j--;
    } else prev = c;
  }
  VRB ("vivify", stats.vivifications,
     "flushed %ld subsumed clauses from vivification schedule", subsumed);
  if (subsumed) {
    schedule.resize (j - schedule.begin ());
    shrink_vector (schedule);
  } else assert (j == end);
}

/*------------------------------------------------------------------------*/

struct better_watch {

  Internal * internal;

  better_watch (Internal * i) : internal (i) { }

  bool operator () (int a, int b) {
    const int av = internal->val (a), bv = internal->val (b);
    if (av >= 0 && bv < 0) return true;
    if (av < 0 && bv >= 0) return false;
    return internal->var (a).trail > internal->var (b).trail;
  }
};

// Depending on whether we try to vivify redundant or irredundant clauses,
// we schedule a clause to be vivified.  For redundant clauses we only try
// to vivify them if they are likely to survive the next 'reduce' operation
// and have not been tried to be vivified before.
//
bool Internal::try_to_vivify_clause (Clause * c, bool redundant) {
  if (c->garbage) return false;
  if (c->redundant && !redundant) return false;
  if (c->redundant && opts.vivifyonce && c->vivified) return false;
  if (c->redundant && !likely_to_be_kept_clause (c)) return false;
  return true;
}

void Internal::vivify_analyze (Clause * start) {
  vector<Clause*> stack;
  stack.push_back (start);
  while (!stack.empty ()) {
    Clause * c = stack.back ();
    stack.pop_back ();
    const_literal_iterator eoc = c->end ();
    LOG (c, "vivify analyze");
    for (const_literal_iterator i = c->begin (); i != eoc; i++) {
      const int lit = *i;
      Var & v = var (lit);
      if (!v.level) continue;
      Flags & f = flags (lit);
      if (f.seen) continue;
      assert (val (lit) < 0);
      f.seen = true;
      analyzed.push_back (lit);
      if (v.reason) stack.push_back (v.reason);
      else LOG ("vivify seen %d", lit);
    }
  }
}

// Two types of vivification rounds, one focusing only on redundant clauses
// and one focusing on irredundant clauses only.  The variant on irredundant
// clauses also removes asymmetric tautologies (clauses subsumed through
// unit propagation), which the redundant round does not.

void Internal::vivify_round (bool redundant, long delta) {

  if (unsat) return;

  VRB ("vivify", stats.vivifications,
    "starting %s vivification round propagation delta %ld",
    redundant ? "redundant" : "irredundant", delta);

  // Disconnect all watches since we sort literals within clauses.
  //
  if (watches ()) disconnect_watches ();

  // Count the number of occurrences of literals in all clauses,
  // particularly binary clauses, which are usually responsible
  // for most of the propagations.
  //
  init_noccs ();

  const const_clause_iterator end = clauses.end ();
  const_clause_iterator i;

  for (i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (!try_to_vivify_clause (c, redundant)) continue;
    const const_literal_iterator eoc = c->end ();
    const_literal_iterator j;

    // This computes an approximation of the Jeroslow Wang heuristic score
    //
    //       nocc (L) =     sum       2^(12-|C|)
    //                   L in C in F
    //
    // but we cap the size at 12, that is all clauses of size 12 and larger
    // contribute '1' to the score, which allows us to use 'long' numbers.
    // See the example above (search for '@1').
    //
    const int shift = 12 - c->size;
    const long score = shift < 1 ? 1 : (1l << shift);		// @4

    for (j = c->begin (); j != eoc; j++)
      noccs (*j) += score;
  }

  // Refill the schedule every time.  Unchecked clauses are 'saved' by
  // setting their 'vivify' bit, such that they can be tried next time.
  //
  vector<Clause*> schedule;

  // In the first round of filling the schedule check whether there are
  // still clauses left, which were scheduled but have not been vivified yet.
  // The second round is only entered if no such clause was found in the
  // first round.  Then the second round selects all clauses.
  //
  for (int round = 0; schedule.empty () && round <= 1; round++) {
    for (i = clauses.begin (); i != end; i++) {
      Clause * c = *i;
      if (c->size == 2) continue;       // see also (NO-BINARY) below
      if (!try_to_vivify_clause (c, redundant)) continue;
      if (!round && !c->vivify) continue;

      // Literals in scheduled clauses are sorted with their highest score
      // literals first (as explained above in the example at '@2').
      //
      sort (c->begin (), c->end (), vivify_more_noccs (this));
      schedule.push_back (c);
      c->vivify = true;
    }
  }
  shrink_vector (schedule);

  // Sort candidates, with first to be tried candidate clause last
  // (many occurrences and high score literals) as in the example
  // explained above (search for '@3').
  //
  stable_sort (schedule.begin (),
               schedule.end (),
	       vivify_less_clause (this, redundant));

  // Counters, for what happened.
  //
  long checked = 0, subsumed = 0, strengthened = 0, units = 0;

  flush_vivification_schedule (schedule, subsumed);
  long scheduled = schedule.size ();
  stats.vivifysched += scheduled;

  VRB ("vivify", stats.vivifications,
    "scheduled %ld clauses to be vivified %.0f%%",
    scheduled, percent (scheduled, stats.irredundant));

  // Limit the number of propagations during vivification as in 'probe'.
  //
  long limit = stats.propagations.vivify + delta;

  connect_watches (!redundant);		// watch all relevant clauses
  vector<int> sorted;			// sort literals of each candidate

  while (!unsat &&
         !schedule.empty () &&
         stats.propagations.vivify < limit) {

    // Next candidate clause to vivify.
    //
    Clause * c = schedule.back ();
    schedule.pop_back ();
    assert (redundant || !c->redundant);
    assert (c->size > 2)	;               // see (NO-BINARY) above
    assert (c->vivify);
    c->vivify = false;
    if (c->garbage) continue;

    // First check whether the candidate clause is already satisfied and at
    // the same time copy its non fixed literals to 'sorted'.  The literals
    // in the candidate clause might not be sorted anymore due to replacing
    // watches during propagation, even though we sorted them initially
    // while pushing the clause onto the schedule and sorting the schedule.
    //
    const const_literal_iterator eoc = c->end ();
    const_literal_iterator j;
    int satisfied = 0;
    sorted.clear ();
    for (j = c->begin (); !satisfied && j != eoc; j++) {
      const int lit = *j, tmp = fixed (lit);
      if (tmp > 0) satisfied = *j;
      else if (!tmp) sorted.push_back (lit);
    }
    if (satisfied) {
      LOG (c, "satisfied by propagated unit %d", satisfied);
      mark_garbage (c);
      continue;
    }
    sort (sorted.begin (), sorted.end (), vivify_more_noccs (this));

    // The actual vivification checking is performed here, by assuming the
    // negation of each of the remaining literals of the clause in turn and
    // propagating it.  If a conflict occurs or another literal in the
    // clause becomes assigned during propagation, we can stop.
    //
    LOG (c, "vivification checking");
    checked++;

    // These are used in the next block and also further down.
    //
    const const_int_iterator eos = sorted.end ();
    const_int_iterator k;

    // If the decision 'level' is non-zero, then we can reuse decisions for
    // the previous candidate, and avoid re-propagating them.  In preliminary
    // experiments this saved between 30%-50% decisions (and thus
    // propagations), which in turn lets us also vivify more clauses within
    // the same propagation bounds, or terminate earlier if vivify runs to
    // completion.
    //
    if (level) {
#ifdef LOGGING
      int orig_level = level;
#endif
      // First check whether this clause is actually a reason for forcing
      // one of its literals to true and then backtrack one level before
      // that happened.  Otherwise this clause might be incorrectly
      // considered to be redundant or if this situation is checked then
      // redundancy by other clauses using this forced literal becomes
      // impossible.
      //
      int forced = 0;

      // This search could be avoided if we would eagerly set the 'reason'
      // boolean flag of clauses, which however we do not want to do for
      // binary clauses (during propagation) and thus would still require
      // a version of 'protect_reason' for binary clauses during 'reduce'
      // (well binary clauses are not collected during 'reduce', but again
      // this exception from the exception is pretty complex and thus a
      // simply search here is probably easier to understand).

      for (j = c->begin (); !forced && j != eoc; j++) {
	const int lit = *j, tmp = val (lit);
	if (tmp < 0) continue;
	if (tmp > 0 && var (lit).reason == c) forced = lit;
	break;
      }
      if (forced) {
	LOG ("clause is reason forcing %d", forced);
	assert (var (forced).level);
	backtrack (var (forced).level - 1);
      }

      // As long the (remaining) literals of the sorted clause match
      // decisions on the trail we just reuse them.
      //
      int l = 1;	// This is the decision level we want to reuse.

      for (k = sorted.begin (); k != eos && l <= level; k++) {
	const int lit = *k;
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

      LOG ("reused %d decision levels from %d", level, orig_level);
    }

    // Make sure to ignore this clause during propagation.  This is not that
    // easy for binary clauses (NO-BINARY), e.g., ignoring binary clauses,
    // without changing 'propagate' and actually we also do not want to
    // remove binary clauses which are subsumed.  Those are hyper binary
    // resolvents and should be kept as learned clauses instead unless they
    // are transitive in the binary implication graph, which in turn is
    // detected during transitive reduction in 'transred'.
    //
    c->ignore = true;           // see also (NO-BINARY) above

    int subsume = 0;            // determined to be redundant / subsumed
    int remove = 0;             // at least literal 'remove' can be removed

    LOG (sorted, "sorted size %ld probing schedule", (long) sorted.size ());

    long * strptr = redundant ? &stats.vivifystred1 : &stats.vivifystrirr;

    for (k = sorted.begin (); !subsume && k != eos; k++) {

      const int lit = *k, tmp = val (lit);

      if (tmp) {		// assigned

	const Var & v = var (lit);

	if (!v.level) { LOG ("skipping fixed %d", lit); continue; }
	if (!v.reason) { LOG ("skipping decision %d", lit); continue; }

	if (tmp > 0) {		// positive implied
	  LOG ("subsumed since literal %d already true", lit);
	  subsume = lit;
	  if (redundant) {
	    assert (clause.empty ());
	    assert (analyzed.empty ());
	    flags (lit).seen = true;
	    analyzed.push_back (-lit);
	    LOG ("vivify seen %d", -lit);
	    assert (v.reason);
	    conflict = v.reason;
	    strptr = &stats.vivifystred2;
	    goto ANALYZE;			// TODO remove GOTO
	  }
	} else {		// negative implied
	  assert (tmp < 0);
	  LOG ("literal %d is already false and can be removed", lit);
	  remove = lit;
	}
      } else {			// still unassigned
	stats.vivifydecs++;
        assume_decision (-lit);
	LOG ("negated decision %d score %ld", lit, noccs (lit));
        if (propagate ()) continue;
        LOG ("subsumed since propagation produced conflict");
        subsume = INT_MIN;

	if (redundant) {
	  strptr = &stats.vivifystred3;
	  assert (clause.empty ());
	  assert (analyzed.empty ());
ANALYZE:
	  LOG ("analyzing conflict in redundant mode");
	  vivify_analyze (conflict);
	  for (j = c->begin (); j != eoc; j++) {
	    const int other = *j;
	    if (other == subsume) continue;
	    if (val (other) >= 0) break;
	    Var & v = var (other);
	    if (!v.level) continue;
	    if (v.reason) break;
	    if (!flags (other).seen) break;
	  }
	  if (j == eoc) {
	    LOG ("analysis all literals decisions thus no strengthening");
	    clause.clear ();
	  } else {
	    for (j = c->begin (); j != eoc; j++) {
	      const int other = *j;
	      int keep;
	      if (other == subsume) keep = 1;
	      else if (val (other) >= 0) keep = -1;
	      else {
		Var & v = var (other);
		if (!v.level) keep = 0;
                else if (v.reason) keep = -1;
	        else if (flags (other).seen) keep = 1;
	        else keep = -1;
	      }
	      if (keep > 0) {
		LOG ("keeping literal %d", other);
		clause.push_back (other);	
		mark_added (other);
	      }
	      if (keep < 0) {
		LOG ("flushing literal %d", other);
		mark_removed (other);
	      }
	      if (!keep)
		LOG ("ignoring literal %d", other);
	    }
	  }
	  clear_seen ();
	}

	assert (level > 0);
	backtrack (level - 1);
        conflict = 0;
      }
    }

    if (subsume) {
      if (redundant) {
	if (!clause.empty ()) {
	  LOG ("strengthening instead of subsuming clause");
	  goto STRENGTHEN;			// TODO remove GOTO
	}
	LOG (c, "ignoring asymmetric tautology in redundant mode");
	if (c->redundant) {
	  c->vivified = true;
	} else {
	  LOG (c, "rescheduling for irredundant round");
	  assert (!c->vivify);
	  c->vivify = true;
	}
      } else {
	subsumed++;
	LOG (c, "redundant asymmetric tautology");
	assert (!c->redundant);
	mark_garbage (c);
      }
    } else if (remove) {

      assert (level);
      assert (clause.empty ());

      // There might be other literals implied to false (or even root level
      // falsified).  Those should be removed in addition to 'remove'.
      //
      for (j = c->begin (); j != eoc; j++) {
        const int other = *j;
	assert (val (other) < 0);
        Var & v = var (other);
        if (!v.level) continue;	// root-level fixed
        if (v.reason) {		// negative implied
          assert (v.level);
          assert (v.reason);
          LOG ("flushing literal %d", other);
          mark_removed (other);
        } else {				// decision or unassigned
          LOG ("keeping literal %d", other);
	  clause.push_back (other);	
	  mark_added (other);
	}
      }

STRENGTHEN:
      assert (!clause.empty ());
      strengthened++;
      *strptr += 1;

      if (clause.size () == 1) {
	backtrack ();
        const int unit = clause[0];
        LOG (c, "vivification shrunken to unit %d", unit);
        assert (!val (unit));
	assign_unit (unit);
        units++;
        bool ok = propagate ();
        if (!ok) learn_empty_clause ();
      } else {

	// Move non-false literals to the front, followed by false literals.
	// False literals are further sorted by reverse assignment order.
	// The goal is to find watches which requires to backtrack as few as
	// possible decision levels.
	//
	sort (clause.begin (), clause.end (), better_watch (this));

	int new_level = level;
	const int lit0 = clause[0], val0 = val (lit0);
	if (val0 < 0) {
	  const int level0 = var (lit0).level;
	  LOG ("1st watch %d negative at level %d", lit0, level0);
	  new_level = level0 - 1;
	}
	const int lit1 = clause[1], val1 = val (lit1);
	if (val1 < 0 &&
	    !(val0 > 0 && var (lit0).level <= var (lit1).level)) {
	  const int level1 = var (lit1).level;
	  LOG ("2nd watch %d negative at level %d", lit1, level1);
	  new_level = level1 - 1;
	}
	if (new_level < level) backtrack (new_level);
	assert (val (lit0) >= 0);
	assert (val (lit1) >= 0 ||
	  (val (lit0) > 0 &&
	   val (lit1) < 0 &&
	   var (lit0).level <= var (lit1).level));
	external->check_learned_clause ();
        Clause * d = new_clause_as (c);
        LOG (c, "before vivification");
        LOG (d, "after vivification");
	(void) d;
      }
      clause.clear ();
      mark_garbage (c);
    } else {
      if (c->redundant) c->vivified = true;
      LOG ("vivification failed");
    }
    assert (c->ignore);
    c->ignore = false;
  }

  if (level) backtrack ();

  if (!unsat) {

    reset_noccs ();
    erase_vector (schedule);
    disconnect_watches ();
    connect_watches ();

    // [RE-PROPAGATE] Since redundant clause were disconnected during
    // propagating vivified units above, and further irredundant clauses
    // are arbitrarily sorted, we have to propagate all literals again after
    // connecting the first two literals in the clauses, in order to
    // reestablish the watching invariant.
    //
    propagated = 0;
    if (!propagate ()) {
      LOG ("propagating vivified units leads to conflict");
      learn_empty_clause ();
    }
  }

  VRB ("vivify", stats.vivifications,
    "checked %ld clauses %.02f%% of %ld scheduled",
    checked, percent (checked, scheduled), scheduled);
  if (units)
  VRB ("vivify", stats.vivifications,
    "found %ld units %.02f%% of %ld checked",
    units, percent (units, checked), checked);
  if (subsumed)
  VRB ("vivify", stats.vivifications,
    "subsumed %ld clauses %.02f%% of %ld checked",
    subsumed, percent (subsumed, checked), checked);
  if (strengthened)
  VRB ("vivify", stats.vivifications,
    "strengthened %ld clauses %.02f%% of %ld checked",
    strengthened, percent (strengthened, checked), checked);

  stats.vivifychecks += checked;
  stats.vivifysubs += subsumed;
  stats.vivifystrs += strengthened;
  stats.vivifyunits += units;

  stats.subsumed += subsumed;
  stats.strengthened += strengthened;

  lim.search_propagations.vivify = stats.propagations.search;
  report ('v');
}

void Internal::vivify () {

  if (unsat) return;

  assert (opts.vivify);
  SWITCH_AND_START (search, simplify, vivify);

  assert (!vivifying);
  vivifying = true;	// forces vivify propagation counting in 'propagate'

  stats.vivifications++;
  if (level) backtrack ();

  long delta = stats.propagations.search;
  delta -= lim.search_propagations.vivify;
  delta *= opts.vivifyreleff;
  if (delta < opts.vivifymineff) delta = opts.vivifymineff;
  if (delta > opts.vivifymaxeff) delta = opts.vivifymaxeff;

  vivify_round (true, delta);
  vivify_round (false, delta);

  lim.search_propagations.vivify = stats.propagations.search;

  assert (vivifying);
  vivifying = false;

  STOP_AND_SWITCH (vivify, simplify, search);
}

};
