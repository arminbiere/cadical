#include "internal.hpp"
#include "kitten.h"
#include "options.hpp"

namespace CaDiCaL {

// Failed literal handling as pioneered by MiniSAT.  This first function
// adds an assumption literal onto the assumption stack.

void Internal::assume (int lit) {
  if (level && !opts.ilb)
    backtrack ();
  else if (val (lit) < 0)
    backtrack_without_updating_phases (max (0, var (lit).level - 1));
  Flags &f = flags (lit);
  const unsigned char bit = bign (lit);
  if (f.assumed & bit) {
    LOG ("ignoring already assumed %d", lit);
    return;
  }
  if (f.constrained && !f.assumed)
    constraints_without_assumptions--;
  LOG ("assume %d", lit);
  f.assumed |= bit;
  assumptions.push_back (lit);
  freeze (lit);
  if (constraint_cat)
    KITTEN_NAMESPACE (kitten_assume_signed (constraint_cat, lit));
}

// for LRAT we implement recursive DFS, for non-LRAT use BFS.
// TODO: maybe derecursify to avoid stack overflow
//
void Internal::assume_analyze_literal (int lit) {
  assert (lit);
  Flags &f = flags (lit);
  if (f.seen)
    return;
  f.seen = true;
  analyzed.push_back (lit);
  Var &v = var (lit);
  assert (val (lit) < 0);
  if (v.reason == external_reason) {
    v.reason = learn_external_reason_clause (-lit, 0, true);
    assert (v.reason || !v.level);
  }
  assert (v.reason != external_reason);
  if (!v.level) {
    int64_t id = unit_id (-lit);
    lrat_chain.push_back (id);
    return;
  }
  if (v.reason) {
    assert (v.level);
    LOG (v.reason, "analyze reason");
    for (const auto &other : *v.reason) {
      assume_analyze_literal (other);
    }
    lrat_chain.push_back (v.reason->id);
    return;
  }
  assert (assumed (-lit));
  LOG ("failed assumption %d", -lit);
  clause.push_back (lit);
}

void Internal::assume_analyze_reason (int lit, Clause *reason) {
  assert (reason);
  assert (lrat_chain.empty ());
  assert (reason != external_reason);
  assert (lrat);
  for (const auto &other : *reason)
    if (other != lit)
      assume_analyze_literal (other);
  lrat_chain.push_back (reason->id);
}

void Internal::mark_failing_assumption (int failed) {
  Flags &f = flags (failed);
  const unsigned bit = bign (failed);
  assert (f.assumed & bit);
  assert (!(f.failed & bit));
  f.failed |= bit;
  failing_assumptions.push_back (failed);
}

extern "C" {

// mark failing assumptions and constraints.
//
static void traverse_constraint_core (void *state, unsigned id) {
  Internal *internal = (Internal *) state;
  // mark failing constraints.
  LOG ("traversing core constraint[%d]", id);
  internal->mark_failed_constraint (id);
}

// extracts relevant learned clauses from kitten for drat proofs
//
static void traverse_constraint_drat (void *state, unsigned id,
                                      bool learned, size_t size,
                                      const unsigned *lits) {
#ifndef LOGGING
  (void) id;
#endif
  Internal *internal = (Internal *) state;
  if (!learned) {
    LOG ("ignore original clause[%d]", id);
    return;
  }
  auto &clause = internal->clause;
  assert (clause.empty ());
  assert (internal->proof);
  assert (!internal->lrat);
  assert (internal->lrat_chain.empty ());
  for (auto &lit : internal->failing_assumptions)
    clause.push_back (internal->externalize (lit));
  for (size_t i = 0; i < size; i++)
    clause.push_back (internal->externalize (internal->cat2lit (lits[i])));
  internal->proof->add_constraint_clause (++internal->clause_id, clause,
                                          internal->lrat_chain);
  internal->conclusion.push_back (internal->clause_id);
  clause.clear ();
}

// extract lrat proofs for relevant clauses
//
static void traverse_constraint_lrat (void *state, unsigned ref,
                                      unsigned id, bool learned,
                                      size_t size, const unsigned *lits,
                                      size_t chain_size,
                                      const unsigned *chain) {
  Internal *internal = (Internal *) state;
  if (!learned) {
    assert (id);
    LOG ("original kitten[%d] = %d", ref, id);
    internal->constraint_refs[ref] = id;
    return;
  }
  assert (!id);
  auto &clause = internal->clause;
  auto &lrat_chain = internal->lrat_chain;
  assert (clause.empty ());
  assert (internal->proof);
  assert (internal->lrat);
  assert (lrat_chain.empty ());
  for (size_t i = 0; i < chain_size; i++) {
    const unsigned kref = chain[i];
    // kid is kitten internal representation,
    // not cadical representation. Mapping needed.
    assert (internal->constraint_refs.find (kref) !=
            internal->constraint_refs.end ());
    const unsigned cid = internal->constraint_refs[kref];
    assert (cid);
    // TODO: mapping from intermediary kitten id to cadical id
    // would allow INT_MAX constraints (also see
    // comment in constrain.cpp)
    lrat_chain.push_back (cid);
  }
  for (size_t i = 0; i < size; i++)
    clause.push_back (internal->externalize (internal->cat2lit (lits[i])));
  const int64_t new_id = ++internal->clause_id;
  reverse (lrat_chain.begin (), lrat_chain.end ());
  // using constraints in the derivation.
  internal->proof->add_constraint_clause (new_id, clause, lrat_chain);
  internal->constraint_refs[ref] = new_id;
  internal->conclusion.push_back (internal->clause_id);
  clause.clear ();
  lrat_chain.clear ();
}

} // end extern C

// Find all failing assumptions starting from the one on the assumption
// stack with the lowest decision level.  This goes back to MiniSAT and is
// called 'analyze_final' there.

void Internal::failing () {

  PROFILE_SCOPE (analyze);

  LOG ("analyzing failing assumptions");

  assert (analyzed.empty ());
  assert (clause.empty ());
  assert (lrat_chain.empty ());
  assert (!marked_failed);
  assert (!unsat);

  if (!unsat_constraint) {
    // Search for failing assumptions in the (internal) assumption stack.

    // There are in essence three cases: (1) An assumption is falsified on
    // the root-level and then 'failed_unit' is set to that assumption, (2)
    // two clashing assumptions are assumed and then 'failed_clashing' is
    // set to the second assumed one, or otherwise (3) there is a failing
    // assumption 'first_failed' with minimum (non-zero) decision level
    // 'failed_level'.

    int failed_unit = 0;
    int failed_clashing = 0;
    int first_failed = 0;
    int failed_level = INT_MAX;
    int efailed = 0;

    for (auto &elit : external->assumptions) {
      int lit = external->e2i[abs (elit)];
      if (elit < 0)
        lit = -lit;
      if (val (lit) >= 0)
        continue;
      const Var &v = var (lit);
      if (!v.level) {
        failed_unit = lit;
        efailed = elit;
        break;
      }
      if (failed_clashing)
        continue;
      if (v.reason == external_reason) {
        Var &ev = var (lit);
        ev.reason = learn_external_reason_clause (-lit);
        if (!ev.reason) {
          ev.level = 0;
          failed_unit = lit;
          efailed = elit;
          break;
        }
        ev.level = 0;
        // Recalculate assignment level
        for (const auto &other : *ev.reason) {
          if (other == -lit)
            continue;
          assert (val (other));
          int tmp = var (other).level;
          if (tmp > ev.level)
            ev.level = tmp;
        }
        if (!ev.level) {
          failed_unit = lit;
          efailed = elit;
          break;
        }
      }
      assert (v.reason != external_reason);
      if (!v.reason) {
        failed_clashing = lit;
        efailed = elit;
      } else if (!first_failed || v.level < failed_level) {
        first_failed = lit;
        efailed = elit;
        failed_level = v.level;
      }
    }

    assert (clause.empty ());

    // Get the 'failed' assumption from one of the three cases.
    int failed;
    if (failed_unit)
      failed = failed_unit;
    else if (failed_clashing)
      failed = failed_clashing;
    else
      failed = first_failed;
    assert (failed);
    assert (efailed);

    // In any case mark literal 'failed' as failed assumption.
    mark_failing_assumption (failed);

    // First case (1).
    if (failed_unit) {
      assert (failed == failed_unit);
      LOG ("root-level falsified assumption %d", failed);
      if (proof) {
        if (lrat) {
          unsigned eidx = (efailed > 0) + 2u * (unsigned) abs (efailed);
          assert ((size_t) eidx < external->ext_units.size ());
          const int64_t id = external->ext_units[eidx];
          if (id) {
            lrat_chain.push_back (id);
          } else {
            int64_t id = unit_id (-failed_unit);
            lrat_chain.push_back (id);
          }
        }
        proof->add_assumption_clause (++clause_id, -efailed, lrat_chain);
        conclusion.push_back (clause_id);
        lrat_chain.clear ();
      }
      return;
    }

    // Second case (2).
    if (failed_clashing) {
      assert (failed == failed_clashing);
      LOG ("clashing assumptions %d and %d", failed, -failed);
      mark_failing_assumption (-failed);
      if (proof) {
        vector<int> clash = {externalize (failed), externalize (-failed)};
        proof->add_assumption_clause (++clause_id, clash, lrat_chain);
        conclusion.push_back (clause_id);
      }
      return;
    }

    // Fall through to third case (3).
    LOG ("starting with assumption %d falsified on minimum decision level "
         "%d",
         first_failed, failed_level);

    assert (first_failed);
    assert (failed_level > 0);

    // The 'analyzed' stack serves as working stack for a BFS through the
    // implication graph until decisions, which are all assumptions, or
    // units are reached.  This is simpler than corresponding code in
    // 'analyze'.
    {
      LOG ("failed assumption %d", first_failed);
      Flags &f = flags (first_failed);
      assert (!f.seen);
      f.seen = true;
      assert (f.failed & bign (first_failed));
      analyzed.push_back (-first_failed);
      clause.push_back (-first_failed);
    }
  } else {
    assert (constraint_cat);
    // unsat_constraint
    // analyze failing constraints with kitten
    uint64_t learned;
    for (auto &lit : assumptions) {
      if (KITTEN_NAMESPACE (kitten_failed_signed) (constraint_cat, lit))
        mark_failing_assumption (lit);
    }
    KITTEN_NAMESPACE (kitten_compute_clausal_core) (constraint_cat,
                                                    &learned);
    KITTEN_NAMESPACE (kitten_traverse_core_ids) (constraint_cat, this,
                                                 traverse_constraint_core);
    // assert (!conclusion.empty ()); breaks if two assumptions contradict
    if (proof) {
      if (conclusion.empty ()) {
        assert (failing_assumptions.size () == 2);
        for (auto &lit : failing_assumptions)
          clause.push_back (externalize (lit));
        proof->add_assumption_clause (++clause_id, clause, lrat_chain);
        conclusion.push_back (clause_id);
      } else if (lrat) {
        assert (constraint_refs.empty ());
        KITTEN_NAMESPACE (kitten_trace_core) (constraint_cat, this,
                                              traverse_constraint_lrat);
        constraint_refs.clear ();
      } else {
        KITTEN_NAMESPACE (kitten_traverse_core_clauses_with_id) (
            constraint_cat, this, traverse_constraint_drat);
      }
    }
  }

  {
    // no LRAT do bfs as it was before
    if (!unsat_constraint && !lrat) {
      size_t next = 0;
      while (next < analyzed.size ()) {
        const int lit = analyzed[next++];
        assert (val (lit) > 0);
        Var &v = var (lit);
        if (!v.level)
          continue;
        if (v.reason == external_reason) {
          v.reason = learn_external_reason_clause (lit, 0, true);
          if (!v.reason) {
            v.level = 0;
            continue;
          }
        }
        assert (v.reason != external_reason);
        if (v.reason) {
          assert (v.level);
          LOG (v.reason, "analyze reason");
          for (const auto &other : *v.reason) {
            Flags &f = flags (other);
            if (f.seen)
              continue;
            f.seen = true;
            assert (val (other) < 0);
            analyzed.push_back (-other);
          }
        } else {
          assert (assumed (lit));
          LOG ("failed assumption %d", lit);
          clause.push_back (-lit);
          mark_failing_assumption (lit);
        }
      }
      clear_analyzed_literals ();
    } else if (!unsat_constraint && lrat) { // LRAT for case (3)
      assert (clause.size () == 1);
      const int lit = clause[0];
      Var &v = var (lit);
      assert (v.reason);
      if (v.reason == external_reason) { // does this even happen?
        v.reason = learn_external_reason_clause (lit, 0, true);
      }
      assert (v.reason != external_reason);
      if (v.reason)
        assume_analyze_reason (lit, v.reason);
      else {
        int64_t id = unit_id (lit);
        lrat_chain.push_back (id);
      }
      for (auto &lit : clause) {
        Flags &f = flags (lit);
        const unsigned bit = bign (-lit);
        if (!(f.failed & bit))
          f.failed |= bit;
      }
      clear_analyzed_literals ();
    } else {
      // LRAT for unsat_constraint is already done
      // TODO: clean up / refactor
    }
    clear_analyzed_literals ();

    // Doing clause minimization here does not do anything because
    // the clause already contains only one literal of each level
    // and minimization can never reduce the number of levels

    VERBOSE (1, "found %zd failed assumptions %.0f%%", clause.size (),
             percent (clause.size (), assumptions.size ()));

    // We do not actually need to learn this clause, since the conflict is
    // forced already by some other clauses.  There is also no bumping
    // of variables nor clauses necessary.  But we still want to check
    // correctness of the claim that the determined subset of failing
    // assumptions are a high-level core or equivalently their negations
    // form a unit-implied clause.
    //
    if (!unsat_constraint) {
      external->check_learned_clause ();
      if (proof) {
        vector<int> eclause;
        for (auto &lit : clause)
          eclause.push_back (externalize (lit));
        proof->add_assumption_clause (++clause_id, eclause, lrat_chain);
        conclusion.push_back (clause_id);
      }
    } else {
      // TODO: clean up / refactor
      // unsat_constraint already computed
    }
    lrat_chain.clear ();
    clause.clear ();
  }
}

bool Internal::failed (int lit) {
  conclude_unsat ();
  Flags &f = flags (lit);
  const unsigned bit = bign (lit);
  return (f.failed & bit) != 0;
}

void Internal::conclude_unsat () {
  if (concluded) {
    assert (marked_failed);
    return;
  }
  concluded = true;
  if (unsat)
    assert (marked_failed && conclusion.size () == 1 &&
            conclusion.back () == unsat);
  else if (!marked_failed) {
    assert (conclusion.empty ());
    failing ();
    marked_failed = true;
  }
  if (!proof)
    return;
  ConclusionType con;
  if (unsat)
    con = CONFLICT;
  else if (unsat_constraint)
    con = CONSTRAINT;
  else
    con = ASSUMPTIONS;
  proof->conclude_unsat (con, conclusion);
}

void Internal::reset_concluded () {
  if (proof)
    proof->reset_assumptions ();
  if (concluded) {
    LOG ("reset concluded");
    concluded = false;
  }
  if (unsat) {
    assert (conclusion.size () == 1);
    return;
  }
  conclusion.clear ();
}

// Add the start of each incremental phase (leaving the state
// 'UNSATISFIABLE' actually) we reset all assumptions.

void Internal::reset_assumptions () {
  for (const auto &lit : assumptions) {
    Flags &f = flags (lit);
    const unsigned char bit = bign (lit);
    f.assumed &= ~bit;
    f.failed &= ~bit;
    melt (lit);
  }
  LOG ("cleared %zd assumptions", assumptions.size ());
  assumptions.clear ();
  failing_assumptions.clear ();
  marked_failed = true;
}

struct sort_assumptions_positive_rank {
  Internal *internal;

  // Decision level could be 'INT_MAX' and thus 'level + 1' could overflow.
  // Therefore we carefully have to use 'unsigned' for levels below.

  const unsigned max_level;

  sort_assumptions_positive_rank (Internal *s)
      : internal (s), max_level (s->level + 1u) {}

  typedef uint64_t Type;

  // Set assumptions first, then sorted by position on the trail
  // unset literals are sorted by literal value.

  Type operator() (const int &a) const {
    const int val = internal->val (a);
    const bool assigned = (val != 0);
    const Var &v = internal->var (a);
    uint64_t res = (assigned ? (unsigned) v.level : max_level);
    res <<= 32;
    res |= (assigned ? v.trail : abs (a));
    return res;
  }
};

struct sort_assumptions_smaller {
  Internal *internal;
  sort_assumptions_smaller (Internal *s) : internal (s) {}
  bool operator() (const int &a, const int &b) const {
    return sort_assumptions_positive_rank (internal) (a) <
           sort_assumptions_positive_rank (internal) (b);
  }
};

// Sort the assumptions by the current position on the trail and backtrack
// to the first place where the assumptions and the current trail differ.

void Internal::sort_and_reuse_assumptions () {
  assert (opts.ilb >= 1);
  if (assumptions.empty ()) {
    if (opts.ilb == 1) {
      LOG ("no assumptions, reusing nothing (ilb == 1)");
      backtrack (0);
    } else { // reuse full trail
      LOG ("no assumptions, reusing everything (ilb == 2)");
      return;
    }
  }
  if (constraint_cat) {
    LOG ("cannot sort assumptions with constraints, reusing nothing");
    backtrack (0);
    return;
  }
  MSORT (opts.radixsortlim, assumptions.begin (), assumptions.end (),
         sort_assumptions_positive_rank (this),
         sort_assumptions_smaller (this));

  unsigned max_level = 0;
  // assumptions are sorted by level, with unset at the end
  for (auto lit : assumptions) {
    if (val (lit))
      max_level = var (lit).level;
    else
      break;
  }

  const unsigned size = min (level + 1u, max_level + 1);
  assert ((size_t) level == control.size () - 1);
  LOG (assumptions, "sorted assumptions");
  int target = 0;
  for (unsigned i = 1, j = 0; i < size;) {
    const Level &l = control[i];
    const int lit = l.decision;
    const int alit = assumptions[j];
    const int lev = i;
    target = lev;
    if (val (alit) > 0 &&
        var (alit).level < lev) { // we can ignore propagated assumptions
      LOG ("ILB skipping propagation %d", alit);
      ++j;
      continue;
    }
    if (!lit) { // skip fake decisions
      target = lev - 1;
      break;
    }
    ++i, ++j;
    assert (var (lit).level == lev || !var (lit).level || var (lit).reason);
    if (l.decision == alit) {
      continue;
    }
    target = lev - 1;
    LOG ("first different literal %d on the trail and %d from the "
         "assumptions",
         lit, alit);
    break;
  }
  if (opts.ilb == 1 &&
      (size_t) target > assumptions.size ()) // reusing only assumptions
    target = assumptions.size ();
  if (target < level)
    backtrack_without_updating_phases (target);
  LOG ("assumptions allow for reuse of trail up to level %d", level);
  if ((size_t) level > assumptions.size ())
    stats.ilb_reuse_assumptions += assumptions.size ();
  else
    stats.ilb_reuse_assumptions += level;
}
} // namespace CaDiCaL
