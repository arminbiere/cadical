#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Vivification is a special case of asymmetric tautology elimination (ATE)
// and asymmetric literal elimination (ALE).  It strengthens and removes
// clauses proven redundant through unit propagation.
//
// The original algorithm is due to a paper by Piette, Hamadi and Sais
// published at ECAI'08.  We have an inprocessing version, e.g., it does not
// necessarily run-to-completion.  Our version also performs conflict
// analysis and uses a new heuristic for selecting clauses to vivify.

// Our idea is to focus on clauses with many occurrences of its literals in
// other clauses first.  This both complements nicely our implementation of
// subsume, which is bounded, e.g., subsumption attempts are skipped for
// very long clauses with literals with many occurrences and also is
// stronger in the sense that it enables to remove more clauses due to unit
// propagation (AT checks).

// While first focusing on irredundant clause we then added a separate phase
// upfront which focuses on strengthening also redundant clauses in spirit
// of the ideas presented in the IJCAI'17 paper by M. Luo, C.-M. Li, F.
// Xiao, F. Manya, and Z. Lu.

// There is another very similar approach called 'distilliation' published
// by Han and Somenzi in DAC'07, which reorganizes the CNF in a trie data
// structure to reuse decisions and propagations along the trie.  We used
// that as an inspiration but instead of building a trie we simple sort
// clauses and literals in such a way that we get the same effect.  If a new
// clause is 'distilled' or 'vivified' we first check how many of the
// decisions (which are only lazily undone) can be reused for that clause.
// Reusing can be improved by picking a global literal order and sorting the
// literals in all clauses with respect to that order.  We favor literals
// with more occurrences first.  Then we sort clauses lexicographically with
// respect to that literal order.

/*------------------------------------------------------------------------*/

// For vivification we have a separate dedicated propagation routine, which
// prefers to propagate binary clauses first.  It also uses its own
// assignment procedure 'vivify_assign', which does not mess with phase
// saving during search nor the conflict and other statistics and further
// can be inlined separately here.  The propagation routine needs to ignore
// (large) clauses which are currently vivified.

inline void Internal::vivify_assign (int lit, Clause * reason) {
  require_mode (VIVIFY);
  const int idx = vidx (lit);
  assert (!vals[idx]);
  assert (!flags (idx).eliminated () || !reason);
  Var & v = var (idx);
  v.level = level;                      // required to reuse decisions
  v.trail = (int) trail.size ();        // used in 'vivify_better_watch'
  v.reason = level ? reason : 0;        // for conflict analysis
  if (!level) learn_unit_clause (lit);
  const signed char tmp = sign (lit);
  vals[idx] = tmp;
  vals[-idx] = -tmp;
  assert (val (lit) > 0);
  assert (val (-lit) < 0);
  trail.push_back (lit);
  LOG (reason, "vivify assign %d", lit);
}

// Assume negated literals in candidate clause.

void Internal::vivify_assume (int lit) {
  require_mode (VIVIFY);
  level++;
  control.push_back (Level (lit, trail.size ()));
  LOG ("vivify decide %d", lit);
  assert (level > 0);
  assert (propagated == trail.size ());
  vivify_assign (lit, 0);
}

// Dedicated routine similar to 'propagate' in 'propagate.cpp' and
// 'probe_propagate' with 'probe_propagate2' in 'probe.cpp'.  Please refer
// to that code for more explanation on how propagation is implemented.

bool Internal::vivify_propagate () {
  require_mode (VIVIFY);
  assert (!unsat);
  START (propagate);
  int64_t before = propagated2 = propagated;
  for (;;) {
    if (propagated2 != trail.size ()) {
      const int lit = -trail[propagated2++];
      LOG ("vivify propagating %d over binary clauses", -lit);
      Watches & ws = watches (lit);
      for (const auto & w : ws) {
        if (!w.binary ()) continue;
        const signed char b = val (w.blit);
        if (b > 0) continue;
        if (b < 0) conflict = w.clause;                 // but continue
        else vivify_assign (w.blit, w.clause);
      }
    } else if (!conflict && propagated != trail.size ()) {
      const int lit = -trail[propagated++];
      LOG ("vivify propagating %d over large clauses", -lit);
      Watches & ws = watches (lit);
      const const_watch_iterator eow = ws.end ();
      const_watch_iterator i = ws.begin ();
      watch_iterator j = ws.begin ();
      while (i != eow) {
        const Watch w = *j++ = *i++;
        if (w.binary ()) continue;
        if (val (w.blit) > 0) continue;
        if (w.clause->garbage) { j--; continue; }
        if (w.clause == ignore) continue;
        literal_iterator lits = w.clause->begin ();
        const int other = lits[0]^lits[1]^lit;
        const signed char u = val (other);
        if (u > 0) j[-1].blit = other;
        else {
          const int size = w.clause->size;
          const const_literal_iterator end = lits + size;
          const literal_iterator middle = lits + w.clause->pos;
          literal_iterator k = middle;
          signed char v = -1;
          int r = 0;
          while (k != end && (v = val (r = *k)) < 0)
            k++;
          if (v < 0) {
            k = lits + 2;
            assert (w.clause->pos <= size);
            while (k != middle && (v = val (r = *k)) < 0)
              k++;
          }
          w.clause->pos = k - lits;
          assert (lits + 2 <= k), assert (k <= w.clause->end ());
          if (v > 0) j[-1].blit = r;
          else if (!v) {
            LOG (w.clause, "unwatch %d in", r);
            lits[0] = other;
            lits[1] = r;
            *k = lit;
            watch_literal (r, lit, w.clause);
            j--;
          } else if (!u) {
            assert (v < 0);
            vivify_assign (other, w.clause);
          } else {
            assert (u < 0);
            assert (v < 0);
            conflict = w.clause;
            break;
          }
        }
      }
      if (j != i) {
        while (i != eow)
          *j++ = *i++;
        ws.resize (j - ws.begin ());
      }
    } else break;
  }
  int64_t delta = propagated2 - before;
  stats.propagations.vivify += delta;
  if (conflict) LOG (conflict, "conflict");
  STOP (propagate);
  return !conflict;
}

/*------------------------------------------------------------------------*/

// Check whether a literal occurs less often.  In the implementation below
// (search for 'int64_t score = ...' or '@4') we actually compute a
// weighted occurrence count similar to the Jeroslow Wang heuristic.

struct vivify_more_noccs {

  Internal * internal;

  vivify_more_noccs (Internal * i) : internal (i) { }

  bool operator () (int a, int b) {
    int64_t n = internal->noccs (a);
    int64_t m = internal->noccs (b);
    if (n > m) return true;     // larger occurrences / score first
    if (n < m) return false;    // smaller occurrences / score last
    if (a == -b) return a > 0;  // positive literal first
    return abs (a) < abs (b);   // smaller index first
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
//  nocc (-2) = 2^12 * (2^-4       ) =  256  7.                 @1
//  nocc ( 3) = 2^12 * (2^-4       ) =  256  8.
//  nocc (-3) = 2^12 * (2^-3 + 2^-3) = 1024  1.
//  nocc ( 4) = 2^12 * (2^-3 + 2^-4) =  768  2.
//  nocc (-4) = 2^12 * (2^-3       ) =  512  5.
//
// which gives the literal order (according to 'vivify_more_noccs')
//
//  -3, 4, 1, 2, -4, -1, -2, 3
//
// Then sorting the literals in each clause gives
//
//  -3  1 -4     (A')
//   4 -1 -2  3  (B')                                           @2
//  -3  4  2     (C')
//
// and finally sorting those clauses lexicographically w.r.t. scores is
//
//  -3  4  2     (C')
//  -3  1 -4     (A')                                           @3
//   4 -1 -2  3  (B')
//
// This order is defined by 'vivify_clause_later' which returns 'true' if
// the first clause should be vivified later than the second.

struct vivify_clause_later {

  Internal * internal;

  vivify_clause_later (Internal * i) : internal (i) { }

  bool operator () (Clause * a, Clause * b) const {

    // First focus on clauses scheduled in the last vivify round but not
    // checked yet since then.
    //
    if (!a->vivify && b->vivify) return true;
    if (a->vivify && !b->vivify) return false;

    // Among redundant clauses (in redundant mode) prefer small glue.
    //
    if (a->redundant) {
      assert (b->redundant);
      if (a->glue > b->glue) return true;
      if (a->glue < b->glue) return false;
    }

    // Then prefer shorter size.
    //
    if (a->size > b->size) return true;
    if (a->size < b->size) return false;

    // Now compare literals in the clauses lexicographically with respect to
    // the literal order 'vivify_more_noccs' assuming literals are sorted
    // decreasingly with respect to that order.
    //
    const auto eoa = a->end (), eob = b->end ();
    auto j = b->begin ();
    for (auto i = a->begin (); i != eoa && j != eob; i++, j++)
      if (*i != *j) return vivify_more_noccs (internal) (*j, *i);

    return j == eob;    // Prefer shorter clauses to be vivified first.
  }
};

/*------------------------------------------------------------------------*/

// Attempting on-the-fly subsumption during sorting when the last line is
// reached in 'vivify_clause_later' above turned out to be trouble some for
// identical clauses.  This is the single point where 'vivify_clause_later'
// is not asymmetric and would require 'stable' sorting for determinism.  It
// can also not be made 'complete' on-the-fly.  Instead of on-the-fly
// subsumption we thus go over the sorted scheduled in a linear scan
// again and remove certain subsumed clauses (the subsuming clause is
// syntactically a prefix of the subsumed clause), which includes
// those troublesome syntactically identical clauses.

struct vivify_flush_smaller {

  bool operator () (Clause * a, Clause * b) const {

    const auto eoa = a->end (), eob = b->end ();
    auto i = a->begin (), j = b->begin ();
    for (; i != eoa && j != eob; i++, j++)
      if (*i != *j) return *i < *j;

    return j == eob && i != eoa;
  }
};

void Internal::flush_vivification_schedule (Vivifier & vivifier) {

  auto & schedule = vivifier.schedule;

  stable_sort (schedule.begin (), schedule.end (), vivify_flush_smaller ());

  const auto end = schedule.end ();
  auto j = schedule.begin (), i = j;

  Clause * prev = 0;
  int64_t subsumed = 0;
  for (; i != end; i++) {
    Clause * c = *j++ = *i;
    if (!prev || c->size < prev->size) { prev = c; continue; }
    const auto eop = prev->end ();
    auto k = prev->begin ();
    for (auto l = c->begin (); k != eop; k++, l++)
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

  if (subsumed)
    PHASE ("vivify", stats.vivifications,
       "flushed %" PRId64 " subsumed scheduled clauses", subsumed);

  stats.vivifysubs += subsumed;

  if (subsumed) {
    schedule.resize (j - schedule.begin ());
    shrink_vector (schedule);
  } else assert (j == end);
}

/*------------------------------------------------------------------------*/

// Depending on whether we try to vivify redundant or irredundant clauses,
// we schedule a clause to be vivified.  For redundant clauses we only try
// to vivify them if they are likely to survive the next 'reduce' operation.

bool Internal::consider_to_vivify_clause (Clause * c,
                                          bool redundant_mode) {
  if (c->garbage) return false;
  if (c->redundant != redundant_mode) return false;
  if (opts.vivifyonce >= 1 && c->redundant && c->vivified) return false;
  if (opts.vivifyonce >= 2 && !c->redundant && c->vivified) return false;
  if (c->redundant && !likely_to_be_kept_clause (c)) return false;
  return true;
}

// Conflict analysis from 'start' which learns a decision only clause.

void Internal::vivify_analyze_redundant (Vivifier & vivifier,
                                         Clause * start,
                                         bool & only_binary_reasons)
{
  LOG ("analyzing conflict in redundant mode");

  only_binary_reasons = true;

  auto & stack = vivifier.stack;
  stack.clear ();

  stack.push_back (start);
  while (!stack.empty ()) {
    Clause * c = stack.back ();
    if (c->size > 2) only_binary_reasons = false;
    stack.pop_back ();
    LOG (c, "vivify analyze");
    for (const auto & lit : *c) {
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

  if (only_binary_reasons) LOG ("all reasons are binary");
}

// Check whether we assigned all literals to false and none is implied.

bool Internal::vivify_all_decisions (Clause * c, int subsume) {

  // assert (redundant_mode);

  for (const auto & other : *c) {
    if (other == subsume) continue;
    if (val (other) >= 0) return false;
    Var & v = var (other);
    if (!v.level) continue;
    if (v.reason) return false;
    if (!flags (other).seen) return false;
  }

  return true;
}

// After conflict analysis (in redundant mode) we check whether all literals
// in the candidate clause 'c' are actually decisions.  If that is case we do
// not subsume the clause 'c'.  Otherwise we go over it and add literals to
// the global learned clause which should be kept.  Thus the result of this
// function is communicated through the global 'clause'.  If it becomes empty,
// we do not learn it and subsumption fails.   The 'subsume' literal is used
// to force keeping that literal (see case '@5' below, where we found this
// positively implied literal).

void Internal::vivify_post_process_analysis (Clause * c, int subsume) {

  // assert (redundant_mode);

  if (vivify_all_decisions (c, subsume)) {

    LOG ("analyzed literals are all decisions thus no strengthening");

    clause.clear ();    // Do not subsume nor strengthen (case '@7').

  } else {              // Otherwise prepare subsuming learned clause.

    for (const auto & other : *c) {

      enum { FLUSH, IGNORE, KEEP } action;

           if (other == subsume)     action = KEEP;
      else if (val (other) >= 0)     action = FLUSH;
      else {
        Var & v = var (other);
             if (!v.level)           action = IGNORE;
        else if (v.reason)           action = FLUSH;
        else if (flags (other).seen) action = KEEP;
        else                         action = FLUSH;
      }

      if (action == KEEP) clause.push_back (other);
#ifdef LOGGING
      if (action == KEEP)   LOG ("keeping literal %d", other);
      if (action == FLUSH)  LOG ("flushing literal %d", other);
      if (action == IGNORE) LOG ("ignoring literal %d", other);
#endif
    }
  }
}

/*------------------------------------------------------------------------*/

// In a strengthened clause the idea is to move non-false literals to the
// front, followed by false literals.  Literals are further sorted by
// reverse assignment order.  The goal is to use watches which require to
// backtrack as few as possible decision levels.

struct vivify_better_watch {

  Internal * internal;

  vivify_better_watch (Internal * i) : internal (i) { }

  bool operator () (int a, int b) {

    const signed char av = internal->val (a), bv = internal->val (b);

    if (av >= 0 && bv < 0) return true;
    if (av < 0 && bv >= 0) return false;

    return internal->var (a).trail > internal->var (b).trail;
  }
};

// Common code to actually strengthen a candidate clause.  The resulting
// strengthened clause is communicated through the global 'clause'.

void Internal::vivify_strengthen (Clause * c) {

  assert (!clause.empty ());
  stats.vivifystrs++;

  if (clause.size () == 1) {

    backtrack ();
    const int unit = clause[0];
    LOG (c, "vivification shrunken to unit %d", unit);
    assert (!val (unit));
    assign_unit (unit);
    stats.vivifyunits++;

    bool ok = propagate ();
    if (!ok) learn_empty_clause ();

  } else {

    // See explanation before 'vivify_better_watch' above.
    //
    sort (clause.begin (), clause.end (), vivify_better_watch (this));

    int new_level = level;

    const int lit0 = clause[0];
    signed char val0 = val (lit0);
    if (val0 < 0) {
      const int level0 = var (lit0).level;
      LOG ("1st watch %d negative at level %d", lit0, level0);
      new_level = level0 - 1;
    }

    const int lit1 = clause[1];
    const signed char val1 = val (lit1);
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

    Clause * d = new_clause_as (c);
    LOG (c, "before vivification");
    LOG (d, "after vivification");
    (void) d;
  }
  clause.clear ();
  mark_garbage (c);
}

/*------------------------------------------------------------------------*/

// Main function: try to vivify this candidate clause in the given mode.

void Internal::vivify_clause (Vivifier & vivifier, Clause * c) {

  const bool redundant_mode = vivifier.redundant_mode;

  assert (redundant_mode || !c->redundant);
  assert (c->size > 2);                       // see (NO-BINARY) below

  c->vivify = false;                          // mark as checked / tried
  c->vivified = true;                         // and globally remember

  if (c->garbage) return;

  // First check whether the candidate clause is already satisfied and at
  // the same time copy its non fixed literals to 'sorted'.  The literals
  // in the candidate clause might not be sorted anymore due to replacing
  // watches during propagation, even though we sorted them initially
  // while pushing the clause onto the schedule and sorting the schedule.
  //
  int satisfied = 0;
  auto & sorted = vivifier.sorted;
  sorted.clear ();

  for (const auto & lit : *c) {
    const int tmp = fixed (lit);
    if (tmp > 0) { satisfied = lit; break; }
    else if (!tmp) sorted.push_back (lit);
  }

  if (satisfied) {
    LOG (c, "satisfied by propagated unit %d", satisfied);
    mark_garbage (c);
    return;
  }

  sort (sorted.begin (), sorted.end (), vivify_more_noccs (this));

  // The actual vivification checking is performed here, by assuming the
  // negation of each of the remaining literals of the clause in turn and
  // propagating it.  If a conflict occurs or another literal in the
  // clause becomes assigned during propagation, we can stop.
  //
  LOG (c, "vivification checking");
  stats.vivifychecks++;

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

    for (const auto & lit : *c) {
      const signed char tmp = val (lit);
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
    if (level) {

      int l = 1;        // This is the decision level we want to reuse.

      for (const auto & lit : sorted) {
	if (fixed (lit)) continue;
	const int decision = control[l].decision;
	if (-lit == decision) {
	  LOG ("reusing decision %d at decision level %d", decision, l);
	  stats.vivifyreused++;
	  if (++l > level) break;
	} else {
	  LOG ("literal %d does not match decision %d at decision level %d",
	    lit, decision, l);
	  backtrack (l-1);
	  break;
	}
      }
    }

    LOG ("reused %d decision levels from %d", level, orig_level);
  }

  LOG (sorted, "sorted size %zd probing schedule", sorted.size ());

  // Make sure to ignore this clause during propagation.  This is not that
  // easy for binary clauses (NO-BINARY), e.g., ignoring binary clauses,
  // without changing 'propagate'. Actually, we do not want to remove binary
  // clauses which are subsumed.  Those are hyper binary resolvents and
  // should be kept as learned clauses instead, unless they are transitive
  // in the binary implication graph, which in turn is detected during
  // transitive reduction in 'transred'.
  //
  ignore = c;

  int subsume = 0;            // determined to be redundant / subsumed
  int remove = 0;             // at least literal 'remove' can be removed

  // If the candidate is redundant, i.e., we are in redundant mode, the
  // clause is subsumed (in one of the two cases below where 'subsume' is
  // assigned) and further all reasons involved are only binary clauses,
  // then this redundant clause is what we once called a hidden tautology,
  // and even for redundant clauses it makes sense to remove the candidate.
  // It does not add anything to propagation power of the formula.  This is
  // the same argument as removing transitive clauses in the binary
  // implication graph during transitive reduction.
  //
  bool only_binary_reasons = false;

  // Go over the literals in the candidate clause in sorted order.
  //
  for (const auto & lit : sorted) {

    // Exit loop as soon a literal is positively implied (case '@5' below)
    // or propagation of the negation of a literal fails ('@6').
    //
    if (subsume) break;

    // We keep on assigning literals, even though we know already that we
    // can remove one (was negatively implied), since we either might run
    // into the 'subsume' case above or more false literals become implied.
    // In any case this might result in stronger vivified clauses.  As a
    // consequence continue with this loop even if 'remove' is non-zero.

    const signed char tmp = val (lit);

    if (tmp) {                // literal already assigned

      const Var & v = var (lit);

      if (!v.level) { LOG ("skipping fixed %d", lit); continue; }
      if (!v.reason) { LOG ("skipping decision %d", lit); continue; }

      if (tmp > 0) {          // positively implied

        LOG ("subsumed since literal %d already true", lit);

        subsume = lit;        // will be able to subsume candidate '@5'

        // In redundant mode we want to strengthen clauses instead of
        // subsuming them (actually incorrect for irredundant candidates).
        // Thus we perform resolutions to find such a strengthening.
        //
        if (redundant_mode) {

          assert (c->redundant);
          assert (clause.empty ());
          assert (analyzed.empty ());

          // We start the analysis by adding the negation of the implied
          // literal to the global 'clause'.
          //
          flags (lit).seen = true;
          analyzed.push_back (-lit);
          LOG ("vivify seen %d", -lit);
          assert (v.reason);

          // Continue the analysis with the reason of the implied literal.
          //
          vivify_analyze_redundant (vivifier, v.reason, only_binary_reasons);
          if (!only_binary_reasons) {
            vivify_post_process_analysis (c, subsume);
            if (!clause.empty ()) stats.vivifystred2++;
          }
          clear_analyzed_literals ();

          backtrack (level - 1);
          assert (!conflict);

          break;
        }

      } else {                // negatively implied

        assert (tmp < 0);
        LOG ("literal %d is already false and can be removed", lit);

        remove = lit;         // will be able to remove this literal
      }

    } else {                  // still unassigned

      stats.vivifydecs++;
      vivify_assume (-lit);
      LOG ("negated decision %d score %" PRId64 "", lit, noccs (lit));

      if (vivify_propagate ()) continue;        // hot-spot

      LOG ("subsumed since propagation produced conflict");

      subsume = INT_MIN;      // will be able to subsume candidate '@6'

      // Again try to strengthen instead of subsuming in redundant mode.
      //
      if (redundant_mode) {

        assert (c->redundant);
        assert (clause.empty ());
        assert (analyzed.empty ());

        vivify_analyze_redundant (vivifier, conflict, only_binary_reasons);
        if (!only_binary_reasons) {
          vivify_post_process_analysis (c, subsume);
          if (!clause.empty ()) stats.vivifystred3++;
        }
        clear_analyzed_literals ();
      }

      backtrack (level - 1);
      conflict = 0;

      break;
    }
  }

  assert (ignore == c);
  ignore = 0;

  if (subsume) {

    if (redundant_mode && !only_binary_reasons) {

      assert (c->redundant);

      if (!clause.empty ()) {

        LOG ("strengthening instead of subsuming clause");
        vivify_strengthen (c);

      } else {  // triggered by '@7'

        // In redundant mode, where candidates might be redundant and we
        // allow to propagate over redundant clauses too, we do not remove
        // unit implied clauses which we failed to strengthen.

        LOG (c, "ignoring asymmetric tautology in redundant mode");

        if (c->redundant) {

          assert (redundant_mode);
          assert (!c->vivify);

        } else {

          // For an irredundant clause the situation is different, since we
          // might be able to remove it even if we only propagate over
          // irredundant clauses.  Thus we schedule it again.

          LOG (c, "rescheduling for irredundant round");
          assert (!c->vivify);

          c->vivify = true;
        }
      }

    } else {

      stats.vivifysubs++;
      LOG (c, "redundant asymmetric tautology");
      mark_garbage (c);

    }

  } else if (remove) {

    assert (level);
    assert (clause.empty ());

    // There might be other literals implied to false (or even root level
    // falsified).  Those should be removed in addition to 'remove'.
    //
    for (const auto & other : *c) {
      assert (val (other) < 0);
      Var & v = var (other);
      if (!v.level) continue; // Remove root-level fixed literals.
      if (v.reason) {         // Remove all negative implied literals.
        assert (v.level);
        assert (v.reason);
        LOG ("flushing literal %d", other);
      } else {                                // Decision or unassigned.
        LOG ("keeping literal %d", other);
        clause.push_back (other);
      }
    }

    if (redundant_mode) stats.vivifystred1++;
    else                stats.vivifystrirr++;

    vivify_strengthen (c);

  } else {
    LOG ("vivification failed");
  }
}

/*------------------------------------------------------------------------*/

// There are two modes of vivification, one using all clauses and one
// focusing on irredundant clauses only.  The latter variant working on
// irredundant clauses only can also remove irredundant asymmetric
// tautologies (clauses subsumed through unit propagation), which in
// redundant mode is incorrect (due to propagating over redundant clauses).

void Internal::vivify_round (bool redundant_mode, int64_t propagation_limit) {

  if (unsat) return;
  if (terminated_asynchronously ()) return;

  PHASE ("vivify", stats.vivifications,
    "starting %s vivification round propagation limit %" PRId64 "",
    redundant_mode ? "redundant" : "irredundant", propagation_limit);

  // Disconnect all watches since we sort literals within clauses.
  //
  if (watching ()) clear_watches ();

  // Count the number of occurrences of literals in all clauses,
  // particularly binary clauses, which are usually responsible
  // for most of the propagations.
  //
  init_noccs ();

  for (const auto & c : clauses) {

    if (!consider_to_vivify_clause (c, redundant_mode)) continue;

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
    const int64_t score = shift < 1 ? 1 : (1l << shift);           // @4

    for (const auto lit : *c)
      noccs (lit) += score;
  }

  // Refill the schedule every time.  Unchecked clauses are 'saved' by
  // setting their 'vivify' bit, such that they can be tried next time.
  //
  Vivifier vivifier (redundant_mode);

  // In the first round of filling the schedule check whether there are
  // still clauses left, which were scheduled but have not been vivified yet.
  // The second round is only entered if no such clause was found in the
  // first round.  Then the second round selects all clauses.
  //
  for (const auto & c : clauses) {

    if (c->size == 2) continue;       // see also (NO-BINARY) above

    if (!consider_to_vivify_clause (c, redundant_mode)) continue;

    // Literals in scheduled clauses are sorted with their highest score
    // literals first (as explained above in the example at '@2').  This
    // is also needed in the prefix subsumption checking below.
    //
    sort (c->begin (), c->end (), vivify_more_noccs (this));

    vivifier.schedule.push_back (c);
  }
  shrink_vector (vivifier.schedule);

  // Flush clauses subsumed by another clause with the same prefix, which
  // also includes flushing syntactically identical clauses.
  //
  flush_vivification_schedule (vivifier);

  // Sort candidates, with first to be tried candidate clause last, i.e.,
  // many occurrences and high score literals) as in the example explained
  // above (search for '@3').
  //
  stable_sort (vivifier.schedule.begin (), vivifier.schedule.end (),
    vivify_clause_later (this));

  // Remember old values of counters to summarize after each round with
  // verbose messages what happened in that round.
  //
  int64_t checked      = stats.vivifychecks;
  int64_t subsumed     = stats.vivifysubs;
  int64_t strengthened = stats.vivifystrs;
  int64_t units        = stats.vivifyunits;

  int64_t scheduled = vivifier.schedule.size ();
  stats.vivifysched += scheduled;

  PHASE ("vivify", stats.vivifications,
    "scheduled %" PRId64 " clauses to be vivified %.0f%%",
    scheduled, percent (scheduled, stats.current.irredundant));

  // Limit the number of propagations during vivification as in 'probe'.
  //
  const int64_t limit = stats.propagations.vivify + propagation_limit;

  connect_watches (!redundant_mode);       // watch all relevant clauses

  if (!unsat && !propagate ()) {
    LOG ("propagation after connecting watches in inconsistency");
    learn_empty_clause ();
  }

  while (!unsat &&
         !terminated_asynchronously () &&
         !vivifier.schedule.empty () &&
         stats.propagations.vivify < limit) {
    Clause * c = vivifier.schedule.back ();              // Next candidate.
    vivifier.schedule.pop_back ();
    vivify_clause (vivifier, c);
  }

  if (level) backtrack ();

  if (!unsat) {

    reset_noccs ();

    int64_t still_need_to_be_vivified = 0;
    for (const auto & c : vivifier.schedule)
      if (c->vivify)
        still_need_to_be_vivified++;

    // Preference clauses scheduled but not vivified yet next time.
    //
    if (still_need_to_be_vivified)
      PHASE ("vivify", stats.vivifications,
        "still need to vivify %" PRId64 " clauses %.02f%% of %" PRId64
        " scheduled", still_need_to_be_vivified,
        percent (still_need_to_be_vivified, scheduled),
        scheduled);
    else {
      PHASE ("vivify", stats.vivifications,
        "no previously not yet vivified clause left");
      for (const auto & c : vivifier.schedule)
        c->vivify = true;
    }

    vivifier.erase ();          // Reclaim  memory early.
  }

  clear_watches ();
  connect_watches ();

  if (!unsat) {

    // Since redundant clause were disconnected during propagating vivified
    // units in redundant mode, and further irredundant clauses are
    // arbitrarily sorted, we have to propagate all literals again after
    // connecting the first two literals in the clauses, in order to
    // reestablish the watching invariant.
    //
    propagated2 = propagated = 0;

    if (!propagate ()) {
      LOG ("propagating vivified units leads to conflict");
      learn_empty_clause ();
    }
  }

  checked      = stats.vivifychecks - checked;
  subsumed     = stats.vivifysubs   - subsumed;
  strengthened = stats.vivifystrs   - strengthened;
  units        = stats.vivifyunits  - units;

  PHASE ("vivify", stats.vivifications,
    "checked %" PRId64 " clauses %.02f%% of %" PRId64 " scheduled",
    checked, percent (checked, scheduled), scheduled);
  if (units)
    PHASE ("vivify", stats.vivifications,
      "found %" PRId64 " units %.02f%% of %" PRId64 " checked",
      units, percent (units, checked), checked);
  if (subsumed)
    PHASE ("vivify", stats.vivifications,
      "subsumed %" PRId64 " clauses %.02f%% of %" PRId64 " checked",
      subsumed, percent (subsumed, checked), checked);
  if (strengthened)
    PHASE ("vivify", stats.vivifications,
      "strengthened %" PRId64 " clauses %.02f%% of %" PRId64 " checked",
      strengthened, percent (strengthened, checked), checked);

  stats.subsumed     += subsumed;
  stats.strengthened += strengthened;

  last.vivify.propagations = stats.propagations.search;

  bool unsuccessful = !(subsumed + strengthened + units);
  report (redundant_mode ? 'w' : 'v', unsuccessful);
}

/*------------------------------------------------------------------------*/

void Internal::vivify () {

  if (unsat) return;
  if (terminated_asynchronously ()) return;
  if (!stats.current.irredundant) return;

  assert (opts.vivify);
  assert (!level);

  START_SIMPLIFIER (vivify, VIVIFY);
  stats.vivifications++;

  int64_t limit = stats.propagations.search;
  limit -= last.vivify.propagations;
  limit *= 1e-3 * opts.vivifyreleff;
  if (limit < opts.vivifymineff) limit = opts.vivifymineff;
  if (limit > opts.vivifymaxeff) limit = opts.vivifymaxeff;

  PHASE ("vivify", stats.vivifications,
    "vivification limit of twice %" PRId64 " propagations", limit);

  vivify_round (false, limit); // Vivify only irredundant clauses.

  limit *= 1e-3 * opts.vivifyredeff;

  vivify_round (true, limit);  // Vivify all clauses.

  STOP_SIMPLIFIER (vivify, VIVIFY);

  last.vivify.propagations = stats.propagations.search;
}

}
