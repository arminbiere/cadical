#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Code for conflict analysis, i.e., to generate the first UIP clause.  The
// main function is 'analyze' below.  It further uses 'minimize' to minimize
// the first UIP clause, which is in 'minimize.cpp'.  An important side
// effect of conflict analysis is to update the decision queue by bumping
// variables.  Similarly analyzed clauses are bumped to mark them as active.

/*------------------------------------------------------------------------*/

void Internal::learn_empty_clause () {
  assert (!unsat);
  LOG ("learned empty clause");
  external->check_learned_empty_clause ();
  if (proof) proof->add_derived_empty_clause ();
  unsat = true;
}

void Internal::learn_unit_clause (int lit) {
  LOG ("learned unit clause %d", lit);
  external->check_learned_unit_clause (lit);
  if (proof) proof->add_derived_unit_clause (lit);
  mark_fixed (lit);
}

/*------------------------------------------------------------------------*/

// Move bumped variables to the front of the (VMTF) decision queue.  The
// 'bumped' time stamp is updated accordingly.  It is used to determine
// whether the 'queue.assigned' pointer has to be moved in 'unassign'.

void Internal::bump_queue (int lit) {
  assert (opts.bump);
  const int idx = vidx (lit);
  if (!links[idx].next) return;
  queue.dequeue (links, idx);
  queue.enqueue (links, idx);
  assert (stats.bumped != INT64_MAX);
  btab[idx] = ++stats.bumped;
  LOG ("moved to front variable %d and bumped to %" PRId64 "", idx, btab[idx]);
  if (!vals[idx]) update_queue_unassigned (idx);
}

/*------------------------------------------------------------------------*/

// It would be better to use 'isinf' but there are some historical issues
// with this function.  On some platforms it is a macro and even for C++ it
// changed the scope (in pre 5.0 gcc) from '::isinf' to 'std::isinf'.  I do
// not want to worry about these strange incompatibilities and thus use the
// same trick as in older solvers (since the MiniSAT team invented EVSIDS)
// and simply put a hard limit here.  It is less elegant but easy to port.

static inline bool evsids_limit_hit (double score) {
  assert (sizeof (score) == 8);	// assume IEEE 754 64-bit double
  return score > 1e150;		// MAX_DOUBLE is around 1.8e308
}

/*------------------------------------------------------------------------*/

// Classical exponential VSIDS as pioneered by MiniSAT.

void Internal::rescore () {
  stats.rescored++;
  double divider = scinc;
  for (int idx = 1; idx <= max_var; idx++) {
    const double tmp = stab[idx];
    if (tmp > divider) divider = tmp;
  }
  PHASE ("rescore", stats.rescored,
    "rescoring %d variable scores by 1/%g", max_var, divider);
  assert (divider > 0);
  double factor = 1.0 / divider;
  for (int idx = 1; idx <= max_var; idx++)
    stab[idx] *= factor;
  scinc *= factor;
  PHASE ("rescore", stats.rescored,
    "new score increment %g after %" PRId64 " conflicts",
    scinc, stats.conflicts);
}

void Internal::bump_score (int lit) {
  assert (opts.bump);
  int idx = vidx (lit);
  double old_score = score (idx);
  assert (!evsids_limit_hit (old_score));
  double new_score = old_score + scinc;
  if (evsids_limit_hit (new_score)) {
    LOG ("bumping %g score of %d hits EVSIDS score limit", old_score, idx);
    rescore ();
    old_score = score (idx);
    assert (!evsids_limit_hit (old_score));
    new_score = old_score + scinc;
  }
  assert (!evsids_limit_hit (new_score));
  LOG ("new %g score of %d", new_score, idx);
  score (idx) = new_score;
  if (scores.contains (idx)) scores.update (idx);
}

// Important variables recently used in conflict analysis are 'bumped',

void Internal::bump_variable (int lit) {
  if (use_scores ()) bump_score (lit);
  else bump_queue (lit);
}

// After every conflict we increase the score increment by a factor.

void Internal::bump_scinc () {
  assert (use_scores ());
  assert (!evsids_limit_hit (scinc));
  double f = 1e3/opts.scorefactor;
  double new_scinc = scinc * f;
  if (evsids_limit_hit (new_scinc)) {
    LOG ("bumping %g increment by %g hits EVSIDS score limit", scinc, f);
    rescore ();
    new_scinc = scinc * f;
  }
  assert (!evsids_limit_hit (new_scinc));
  LOG ("bumped score increment from %g to %g with factor %g",
    scinc, new_scinc, f);
  scinc = new_scinc;
}

/*------------------------------------------------------------------------*/

struct analyze_bumped_rank {
  Internal * internal;
  analyze_bumped_rank (Internal * i) : internal (i) { }
  uint64_t operator () (const int & a) const {
    return internal->bumped (a);
  }
};

struct analyze_bumped_smaller {
  Internal * internal;
  analyze_bumped_smaller (Internal * i) : internal (i) { }
  bool operator () (const int & a, const int & b) const {
    const auto s = analyze_bumped_rank (internal) (a);
    const auto t = analyze_bumped_rank (internal) (b);
    return s < t;
  }
};

/*------------------------------------------------------------------------*/

void Internal::bump_variables () {

  assert (opts.bump);

  START (bump);

  if (opts.bumpreason) bump_also_all_reason_literals ();

  if (!use_scores ()) {

    // Variables are bumped in the order they are in the current decision
    // queue.  This maintains relative order between bumped variables in the
    // queue and seems to work best.  We also experimented with focusing on
    // variables of the last decision level, but results were mixed.

    MSORT (opts.radixsortlim,
      analyzed.begin (), analyzed.end (),
      analyze_bumped_rank (this), analyze_bumped_smaller (this));
  }

  for (const auto & lit : analyzed)
    bump_variable (lit);

  if (use_scores ()) bump_scinc ();

  STOP (bump);
}

/*------------------------------------------------------------------------*/

// Clauses resolved since the last reduction are marked as 'used'.

inline void Internal::bump_clause (Clause * c) {
  LOG (c, "bumping");
  c->used = true;
}

/*------------------------------------------------------------------------*/

// During conflict analysis literals not seen yet either become part of the
// first unique implication point (UIP) clause (if on lower decision level),
// are dropped (if fixed), or are resolved away (if on the current decision
// level and different from the first UIP).  At the same time we update the
// number of seen literals on a decision level.  This helps conflict clause
// minimization.  The number of seen levels is the glucose level (also
// called 'glue', or 'LBD').

inline void
Internal::analyze_literal (int lit, int & open) {
  assert (lit);
  Flags & f = flags (lit);
  if (f.seen) return;
  Var & v = var (lit);
  if (!v.level) return;
  assert (val (lit) < 0);
  assert (v.level <= level);
  if (v.level < level) clause.push_back (lit);
  Level & l = control[v.level];
  if (!l.seen.count++) {
    LOG ("found new level %d contributing to conflict", v.level);
    levels.push_back (v.level);
  }
  if (v.trail < l.seen.trail) l.seen.trail = v.trail;
  f.seen = true;
  analyzed.push_back (lit);
  LOG ("analyzed literal %d assigned at level %d", lit, v.level);
  if (v.level == level) open++;
}

inline void
Internal::analyze_reason (int lit, Clause * reason, int & open) {
  assert (reason);
  bump_clause (reason);
  for (const auto & other : *reason)
    if (other != lit)
      analyze_literal (other, open);
}

/*------------------------------------------------------------------------*/

// This is an idea which was implicit in MapleCOMSPS 2016 for 'limit = 1'.

inline bool Internal::bump_also_reason_literal (int lit) {
  assert (lit);
  assert (val (lit) < 0);
  Flags & f = flags (lit);
  if (f.seen) return false;
  const Var & v = var (lit);
  if (!v.level) return false;
  f.seen = true;
  analyzed.push_back (lit);
  LOG ("bumping also reason literal %d assigned at level %d", lit, v.level);
  return true;
}

inline void Internal::bump_also_reason_literals (int lit, int limit) {
  assert (lit);
  assert (limit > 0);
  const Var & v = var (lit);
  assert (val (lit));
  if (!v.level) return;
  Clause * reason = v.reason;
  if (!reason) return;
  for (const auto & other : *reason) {
    if (other == lit)  continue;
    if (!bump_also_reason_literal (other)) continue;
    if (limit < 2) continue;
    bump_also_reason_literals (-other, limit-1);
  }
}

inline void Internal::bump_also_all_reason_literals () {
  assert (opts.bumpreason);
  assert (opts.bumpreasondepth > 0);
  for (const auto & lit : clause)
    bump_also_reason_literals (-lit, opts.bumpreasondepth);
}

/*------------------------------------------------------------------------*/

void Internal::clear_analyzed_literals () {
  LOG ("clearing %zd analyzed literals", analyzed.size ());
  for (const auto & lit : analyzed) {
    Flags & f = flags (lit);
    assert (f.seen);
    f.seen = false;
    assert (!f.keep);
    assert (!f.poison);
    assert (!f.removable);
  }
  analyzed.clear ();
}

void Internal::clear_analyzed_levels () {
  LOG ("clearing %zd analyzed levels", levels.size ());
  for (const auto & l : levels)
    if (l < (int) control.size ())
      control[l].reset ();
  levels.clear ();
}

/*------------------------------------------------------------------------*/

// Smaller level and trail.  Comparing literals on their level is necessary
// for chronological backtracking, since trail order might in this case not
// respect level order.

struct analyze_trail_negative_rank {
  Internal * internal;
  analyze_trail_negative_rank (Internal * s) : internal (s) { }
  uint64_t operator () (int a) {
    Var & v = internal->var (a);
    uint64_t res = v.level;
    res <<= 32;
    res |= v.trail;
    return ~res;
  }
};

struct analyze_trail_larger {
  Internal * internal;
  analyze_trail_larger (Internal * s) : internal (s) { }
  bool operator () (const int & a, const int & b) const {
    return
      analyze_trail_negative_rank (internal) (a) <
      analyze_trail_negative_rank (internal) (b);
  }
};

/*------------------------------------------------------------------------*/

// Generate new driving clause and compute jump level.

Clause * Internal::new_driving_clause (const int glue, int & jump) {

  const size_t size = clause.size ();
  Clause * res;

  if (!size) {

    jump = 0;
    res = 0;

  } else if (size == 1) {

    iterating = true;
    jump = 0;
    res = 0;

  } else {

    assert (clause.size () > 1);

    // We have to get the last assigned literals into the watch position.
    // Sorting all literals with respect to reverse assignment order is
    // overkill but seems to get slightly faster run-time.  For 'minimize'
    // we sort the literals to heuristically along the trail order (so in
    // the opposite order) with the hope to hit the recursion limit less
    // frequently.  Thus sorting effort is doubled here.
    //
    MSORT (opts.radixsortlim,
      clause.begin (), clause.end (),
      analyze_trail_negative_rank (this), analyze_trail_larger (this));

    jump = var (clause[1]).level;
    res = new_learned_redundant_clause (glue);
    bump_clause (res);
  }

  LOG ("jump level %d", jump);

  return res;
}

/*------------------------------------------------------------------------*/

// If chronological backtracking is enabled we need to find the actual
// conflict level and then potentially can also reuse the conflict clause
// as driving clause instead of deriving a redundant new driving clause
// (forcing 'forced') if the number 'count' of literals in conflict assigned
// at the conflict level is exactly one.

inline int Internal::find_conflict_level (int & forced) {

  assert (conflict);
  assert (opts.chrono);

  int res = 0, count = 0;

  forced = 0;

  for (const auto & lit : *conflict) {
    const int tmp = var (lit).level;
    if (tmp > res) {
      res = tmp;
      forced = lit;
      count = 1;
    } else if (tmp == res) {
      count++;
      if (res == level && count > 1)
        break;
    }
  }

  LOG ("%d literals on actual conflict level %d", count, res);

  const int size = conflict->size;
  int * lits = conflict->literals;

  // Move the two highest level literals to the front.
  //
  for (int i = 0; i < 2; i++) {

    const int lit = lits[i];

    int highest_position = i;
    int highest_literal = lit;
    int highest_level = var (highest_literal).level;

    for (int j = i + 1; j < size; j++) {
      const int other = lits[j];
      const int tmp = var (other).level;
      if (highest_level >= tmp) continue;
      highest_literal = other;
      highest_position = j;
      highest_level = tmp;
      if (highest_level == res) break;
      if (i && highest_level == res - 1) break;
    }

    // No unwatched higher assignment level literal.
    //
    if (highest_position < 2) continue;

    LOG (conflict, "unwatch %d in", lit);
    remove_watch (watches (lit), conflict);
    lits[highest_position] = lit;
    lits[i] = highest_literal;
    watch_literal (highest_literal, lits[!i], conflict);
  }

  // Only if the number of highest level literals in the conflict is one
  // then we can reuse the conflict clause as driving clause for 'forced'.
  //
  if (count != 1) forced = 0;

  return res;
}

/*------------------------------------------------------------------------*/

inline int Internal::determine_actual_backtrack_level (int jump) {

  int res;

  assert (level > jump);

  if (!opts.chrono) {
    res = jump;
    LOG ("chronological backtracking disabled using jump level %d", res);
  } else if (opts.chronoalways) {
    stats.chrono++;
    res = level - 1;
    LOG ("forced chronological backtracking to level %d", res);
  } else if (jump >= level - 1) {
    res = jump;
    LOG ("jump level identical to chronological backtrack level %d", res);
  } else if ((size_t) jump < assumptions.size ()) {
    res = jump;
    LOG ("using jump level %d since it is lower than assumption level %zd",
      res, assumptions.size ());
  } else if (level - jump > opts.chronolevelim) {
    stats.chrono++;
    res = level - 1;
    LOG ("back-jumping over %d > %d levels prohibited"
      "thus backtracking chronologically to level %d",
      level - jump, opts.chronolevelim, res);
  } else if (opts.chronoreusetrail) {

    int best_idx = 0, best_pos = 0;

    if (use_scores ()) {
      for (size_t i = control[jump + 1].trail; i < trail.size (); i++) {
        const int idx = abs (trail[i]);
        if (best_idx && !score_smaller (this) (best_idx, idx)) continue;
        best_idx = idx;
        best_pos = i;
      }
      LOG ("best variable score %g", score (best_idx));
    } else {
      for (size_t i = control[jump + 1].trail; i < trail.size (); i++) {
        const int idx = abs (trail[i]);
        if (best_idx && bumped (best_idx) >= bumped (idx)) continue;
        best_idx = idx;
        best_pos = i;
      }
      LOG ("best variable bumped %" PRId64 "", bumped (best_idx));
    }
    assert (best_idx);
    LOG ("best variable %d at trail position %d", best_idx, best_pos);

    // Now find the frame and decision level in the control stack of that
    // best variable index.  Note that, as in 'reuse_trail', the frame
    // 'control[i]' for decision level 'i' contains the trail before that
    // decision level, i.e., the decision 'control[i].decision' sits at
    // 'control[i].trail' in the trail and we thus have to check the level
    // of the control frame one higher than at the result level.
    //
    res = jump;
    while (res < level-1 && control[res+1].trail <= best_pos)
      res++;

    if (res == jump)
      LOG ("default non-chronological back-jumping to level %d", res);
    else {
      stats.chrono++;
      LOG ("chronological backtracking to level %d to reuse trail", res);
    }

  } else {
    res = jump;
    LOG ("non-chronological back-jumping to level %d", res);
  }

  return res;
}

/*------------------------------------------------------------------------*/

void Internal::eagerly_subsume_recently_learned_clauses (Clause * c) {
  assert (opts.eagersubsume);
  LOG (c, "trying eager subsumption with");
  mark (c);
  int64_t lim = stats.eagertried + opts.eagersubsumelim;
  const auto begin = clauses.begin ();
  auto it = clauses.end ();
#ifdef LOGGING
  int64_t before = stats.eagersub;
#endif
  while (it != begin && stats.eagertried++ <= lim) {
    Clause * d =  *--it;
    if (c == d) continue;
    if (d->garbage) continue;
    if (!d->redundant) continue;
    int needed = c->size;
    for (auto & lit : *d) {
      if (marked (lit) <= 0) continue;
      if (!--needed) break;
    }
    if (needed) continue;
    LOG (d, "eager subsumed");
    stats.eagersub++;
    stats.subsumed++;
    mark_garbage (d);
  }
  unmark (c);
#ifdef LOGGING
  uint64_t subsumed = stats.eagersub - before;
  if (subsumed) LOG ("eagerly subsumed %d clauses", subsumed);
#endif
}

/*------------------------------------------------------------------------*/

// This is the main conflict analysis routine.  It assumes that a conflict
// was found.  Then we derive the 1st UIP clause, optionally minimize it,
// add it as learned clause, and then uses the clause for conflict directed
// back-jumping and flipping the 1st UIP literal.  In combination with
// chronological backtracking (see discussion above) the algorithm becomes
// slightly more involved.

void Internal::analyze () {

  START (analyze);

  assert (conflict);

  // First update moving averages of trail height at conflict.
  //
  UPDATE_AVERAGE (averages.current.trail.fast, trail.size ());
  UPDATE_AVERAGE (averages.current.trail.slow, trail.size ());

  /*----------------------------------------------------------------------*/

  if (opts.chrono) {

    int forced;

    const int conflict_level = find_conflict_level (forced);

    // In principle we can perform conflict analysis as in non-chronological
    // backtracking except if there is only one literal with the maximum
    // assignment level in the clause.  Then standard conflict analysis is
    // unnecessary and we can use the conflict as a driving clause.  In the
    // pseudo code of the SAT'18 paper on chronological backtracking this
    // corresponds to the situation handled in line 4-6 in Alg. 1, except
    // that the pseudo code in the paper only backtracks while we eagerly
    // assign the single literal on the highest decision level.

    if (forced) {

      assert (forced);
      assert (conflict_level > 0);
      LOG ("single highest level literal %d", forced);

      // The pseudo code in the SAT'18 paper actually backtracks to the
      // 'second highest decision' level, while their code backtracks
      // to 'conflict_level-1', which is more in the spirit of chronological
      // backtracking anyhow and thus we also do the latter.
      //
      backtrack (conflict_level - 1);

      LOG ("forcing %d", forced);
      search_assign_driving (forced, conflict);

      conflict = 0;
      STOP (analyze);
      return;
    }

    // Backtracking to the conflict level is in the pseudo code in the
    // SAT'18 chronological backtracking paper, but not in their actual
    // implementation.  In principle we do not need to backtrack here.
    // However, as a side effect of backtracking to the conflict level we
    // set 'level' to the conflict level which then allows us to reuse the
    // old 'analyze' code as is.  The alternative (which we also tried but
    // then abandoned) is to use 'conflict_level' instead of 'level' in the
    // analysis, which however requires to pass it to the 'analyze_reason'
    // and 'analyze_literal' functions.
    //
    backtrack (conflict_level);
  }

  // Actual conflict on root level, thus formula unsatisfiable.
  //
  if (!level) {
    learn_empty_clause ();
    STOP (analyze);
    return;
  }

  /*----------------------------------------------------------------------*/

  // First derive the 1st UIP clause by going over literals assigned on the
  // current decision level.  Literals in the conflict are marked as 'seen'
  // as well as all literals in reason clauses of already 'seen' literals on
  // the current decision level.  Thus the outer loop starts with the
  // conflict clause as 'reason' and then uses the 'reason' of the next
  // seen literal on the trail assigned on the current decision level.
  // During this process maintain the number 'open' of seen literals on the
  // current decision level with not yet processed 'reason'.  As soon 'open'
  // drops to one, we have found the first unique implication point.  This
  // is sound because the topological order in which literals are processed
  // follows the assignment order and a more complex algorithm to find
  // articulation points is not necessary.
  //
  Clause * reason = conflict;
  LOG (reason, "analyzing conflict");

  assert (clause.empty ());

  int i = trail.size ();        // Start at end-of-trail.
  int open = 0;                 // Seen but not processed on this level.
  int uip = 0;                  // The first uip literal.

  for (;;) {
    analyze_reason (uip, reason, open);
    uip = 0;
    while (!uip) {
      assert (i > 0);
      const int lit = trail[--i];
      if (!flags (lit).seen) continue;
      if (var (lit).level == level) uip = lit;
    }
    if (!--open) break;
    reason = var (uip).reason;
    LOG (reason, "analyzing %d reason", uip);
  }
  LOG ("first UIP %d", uip);
  clause.push_back (-uip);

  // Update glue statistics.
  //
  const int glue = (int) levels.size ();
  LOG (clause, "1st UIP size %zd and glue %d clause",
    clause.size (), glue);
  UPDATE_AVERAGE (averages.current.glue.fast, glue);
  UPDATE_AVERAGE (averages.current.glue.slow, glue);

  // Update decision heuristics.
  //
  if (opts.bump) bump_variables ();

  // Update learned = 1st UIP literals counter.
  //
  int size = (int) clause.size ();
  stats.learned.literals += size;
  stats.learned.clauses++;

  // Minimize the 1st UIP clause as pioneered by Niklas Soerensson in
  // MiniSAT and described in our joint SAT'09 paper.
  //
  if (size > 1) {
    if (opts.minimize) minimize_clause ();
    size = (int) clause.size ();
  }

  // Update actual size statistics.
  //
  stats.units    += (size == 1);
  stats.binaries += (size == 2);
  UPDATE_AVERAGE (averages.current.size, size);

  // Determine back-jump level, learn driving clause, backtrack and assign
  // flipped 1st UIP literal.
  //
  int jump;
  Clause * driving_clause = new_driving_clause (glue, jump);
  UPDATE_AVERAGE (averages.current.jump, jump);

  int new_level = determine_actual_backtrack_level (jump);;
  UPDATE_AVERAGE (averages.current.level, new_level);
  backtrack (new_level);

  if (uip) search_assign_driving (-uip, driving_clause);
  else learn_empty_clause ();

  if (stable) reluctant.tick (); // Reluctant has its own 'conflict' counter.

  // Clean up.
  //
  clear_analyzed_literals ();
  clear_analyzed_levels ();
  clause.clear ();
  conflict = 0;

  STOP (analyze);

  if (driving_clause && opts.eagersubsume)
    eagerly_subsume_recently_learned_clauses (driving_clause);
}

// We wait reporting a learned unit until propagation of that unit is
// completed.  Otherwise the 'i' report gives the number of remaining
// variables before propagating the unit (and hides the actual remaining
// variables after propagating it).

void Internal::iterate () { iterating = false; report ('i'); }

}
