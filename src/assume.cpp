#include "internal.hpp"

namespace CaDiCaL {

// Failed literal handling as pioneered by MiniSAT.  This first function
// adds an assumption literal onto the assumption stack.

void Internal::assume (int lit) {
  Flags & f = flags (lit);
  const unsigned char bit = bign (lit);
  if (f.assumed & bit) {
    LOG ("ignoring already assumed %d", lit);
    return;
  }
  LOG ("assume %d", lit);
  f.assumed |= bit;
  assumptions.push_back (lit);
  freeze (lit);
}

// Find all failing assumptions starting from the one on the assumption
// stack with the lowest decision level.  This goes back to MiniSAT and is
// called 'analyze_final' there.  We always return '20' to simplify the code
// in the main search loop in 'Internal::search', which also terminates it.

void Internal::failing () {

  START (analyze);

  LOG ("analyzing failing assumptions");

  assert (analyzed.empty ());
  assert (clause.empty ());

  int first = 0;

  // Try to find two clashing assumptions.
  //
  for (auto & lit : assumptions) {
    if (!assumed (-lit)) continue;
    first = lit;
    break;
  }

  if (first) {

    clause.push_back (first);
    clause.push_back (-first);

    Flags & f = flags (first);

    unsigned bit = bign (first);
    assert (!(f.failed & bit));
    f.failed |= bit;
    bit = bign (-first);
    f.failed |= bit;

  } else {

    // Find an assumption falsified at smallest decision level.
    //
    for (auto & lit : assumptions) {
      const int tmp = val (lit);
      if (tmp >= 0) continue;
      if (!first || var (first).level > var (lit).level)
        first = lit;
    }
    assert (first);
    LOG ("starting with assumption %d falsified on decision level %d",
      first, var (first).level);

    if (!var (first).level) {

      LOG ("failed assumption %d", first);
      clause.push_back (-first);

      Flags & f = flags (first);
      const unsigned bit = bign (first);
      assert (!(f.failed & bit));
      f.failed |= bit;

    } else {

      // The 'analyzed' stack serves as working stack for a BFS through the
      // implication graph until decisions, which are all assumptions, or units
      // are reached.  This is simpler than corresponding code in 'analyze'.

      {
        LOG ("failed assumption %d", first);
        Flags & f = flags (first);
        const unsigned bit = bign (first);
        assert (!(f.failed & bit));
        f.failed |= bit;
        f.seen = true;
      }

      analyzed.push_back (first);
      clause.push_back (-first);

      size_t next = 0;

      while (next < analyzed.size ()) {
        const int lit = analyzed[next++];
#ifndef NDEBUG
        if (first == lit) assert (val (lit) < 0);
        else assert (val (lit) > 0);
#endif
        Var & v = var (lit);
        if (!v.level) continue;

        if (v.reason) {
          assert (v.level);
          LOG (v.reason, "analyze reason");
          for (const auto & other : *v.reason) {
            Flags & f = flags (other);
            if (f.seen) continue;
            f.seen = true;
            assert (val (other) < 0);
            analyzed.push_back (-other);
          }
        } else {
          assert (assumed (lit));
          LOG ("failed assumption %d", lit);
          clause.push_back (-lit);
          Flags & f = flags (lit);
          const unsigned bit = bign (lit);
          assert (!(f.failed & bit));
          f.failed |= bit;
        }
      }
      clear_analyzed_literals ();

      // TODO, we can not do clause minimization here, right?
    }
  }

  VERBOSE (1, "found %zd failed assumptions %.0f%%",
    clause.size (), percent (clause.size (), assumptions.size ()));

  // We do not actually need to learn this clause, since the conflict is
  // forced already by some other clauses.  There is also no bumping
  // of variables nor clauses necessary.  But we still want to check
  // correctness of the claim that the determined subset of failing
  // assumptions are a high-level core or equivalently their negations form
  // a unit-implied clause.
  //
  external->check_learned_clause ();
  if (proof) {
    proof->add_derived_clause (clause);
    proof->delete_clause (clause);
  }
  clause.clear ();

  STOP (analyze);
}

// Add the start of each incremental phase (leaving the state
// 'UNSATISFIABLE' actually) we reset all assumptions.

void Internal::reset_assumptions () {
  for (const auto & lit : assumptions) {
    Flags & f = flags (lit);
    const unsigned char bit = bign (lit);
    f.assumed &= ~bit;
    f.failed &= ~bit;
    melt (lit);
  }
  LOG ("cleared %zd assumptions", assumptions.size ());
  assumptions.clear ();
}

}
