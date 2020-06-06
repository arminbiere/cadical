#include "internal.hpp"

namespace CaDiCaL {

void External::push_zero_on_extension_stack () {
  extension.push_back (0);
  LOG ("pushing 0 on extension stack");
}

void External::push_clause_literal_on_extension_stack (int ilit) {
  assert (ilit);
  const int elit = internal->externalize (ilit);
  assert (elit);
  extension.push_back (elit);
  LOG ("pushing clause literal %d on extension stack (internal %d)",
    elit, ilit);
}

void External::push_witness_literal_on_extension_stack (int ilit) {
  assert (ilit);
  const int elit = internal->externalize (ilit);
  assert (elit);
  extension.push_back (elit);
  LOG ("pushing witness literal %d on extension stack (internal %d)",
    elit, ilit);
  if (marked (witness, elit)) return;
  LOG ("marking witness %d", elit);
  mark (witness, elit);
}

// The extension stack allows to reconstruct a satisfying assignment for the
// original formula after removing eliminated clauses.  This was pioneered
// by Niklas Soerensson in MiniSAT and for instance is described in our
// inprocessing paper, published at IJCAR'12.  This first function adds a
// clause to this stack.  First the blocking or eliminated literal is added,
// and then the rest of the clause.

void External::push_clause_on_extension_stack (Clause * c) {
  internal->stats.weakened++;
  internal->stats.weakenedlen += c->size;
  push_zero_on_extension_stack ();
  for (const auto & lit : *c)
    push_clause_literal_on_extension_stack (lit);
}

void External::push_clause_on_extension_stack (Clause * c, int pivot) {
  push_zero_on_extension_stack ();
  push_witness_literal_on_extension_stack (pivot);
  push_clause_on_extension_stack (c);
}

void
External::push_binary_clause_on_extension_stack (int pivot, int other) {
  internal->stats.weakened++;
  internal->stats.weakenedlen += 2;
  push_zero_on_extension_stack ();
  push_witness_literal_on_extension_stack (pivot);
  push_zero_on_extension_stack ();
  push_clause_literal_on_extension_stack (pivot);
  push_clause_literal_on_extension_stack (other);
}

/*------------------------------------------------------------------------*/

void External::push_external_clause_and_witness_on_extension_stack (
  const vector<int> & c, const vector<int> & w) {
  extension.push_back (0);
  for (const auto & elit : w) {
    assert (elit != INT_MIN);
    init (abs (elit));
    extension.push_back (elit);
    mark (witness, elit);
  }
  extension.push_back (0);
  for (const auto & elit : c) {
    assert (elit != INT_MIN);
    init (abs (elit));
    extension.push_back (elit);
  }
}

/*------------------------------------------------------------------------*/

// This is the actual extension process. It goes backward over the clauses
// on the extension stack and flips the assignment of one of the blocking
// literals in the conditional autarky stored before the clause.  In the
// original algorithm for witness construction for variable elimination and
// blocked clause removal the conditional autarky consists of a single
// literal from the removed clause, while in general the autarky witness can
// contain an arbitrary set of literals.  We are using the more general
// witness reconstruction here which for instance would also work for
// super-blocked or set-blocked clauses.

void External::extend () {

  assert (!extended);
  START (extend);
  internal->stats.extensions++;

  PHASE ("extend", internal->stats.extensions,
    "mapping internal %d assignments to %d assignments",
    internal->max_var, max_var);

  int64_t updated = 0;
  for (unsigned i = 1; i <= (unsigned) max_var; i++) {
    const int ilit = e2i[i];
    if (!ilit) continue;
    while (i >= vals.size ())
      vals.push_back (false);
    vals[i] = (internal->val (ilit) > 0);
    updated++;
  }
  PHASE ("extend", internal->stats.extensions,
    "updated %" PRId64 " external assignments", updated);
  PHASE ("extend", internal->stats.extensions,
    "extending through extension stack of size %zd",
    extension.size ());
  const auto begin = extension.begin ();
  auto i = extension.end ();
  int64_t flipped = 0;
  while (i != begin) {
    bool satisfied = false;
    int lit;
    assert (i != begin);
    while ((lit = *--i)) {
      if (satisfied) continue;
      if (ival (lit) > 0) satisfied = true;
      assert (i != begin);
    }
    assert (i != begin);
    if (satisfied)
      while (*--i)
        assert (i != begin);
    else {
      while ((lit = *--i)) {
        const int tmp = ival (lit);             // not 'signed char'!!!
        if (tmp < 0) {
          LOG ("flipping blocking literal %d", lit);
          assert (lit);
          assert (lit != INT_MIN);
          int idx = abs (lit);
          while ((size_t) idx >= vals.size ())
            vals.push_back (false);
          vals[idx] = !vals[idx];
          internal->stats.extended++;
          flipped++;
        }
        assert (i != begin);
      }
    }
  }
  PHASE ("extend", internal->stats.extensions,
    "flipped %" PRId64 " literals during extension", flipped);
  extended = true;
  LOG ("extended");
  STOP (extend);
}

/*------------------------------------------------------------------------*/

bool External::traverse_witnesses_backward (WitnessIterator & it) {
  if (internal->unsat) return true;
  vector<int> clause, witness;
  const auto begin = extension.begin ();
  auto i = extension.end ();
  while (i != begin) {
    int lit;
    while ((lit = *--i))
      clause.push_back (lit);
    while ((lit = *--i))
      witness.push_back (lit);
    reverse (clause.begin (), clause.end ());
    reverse (witness.begin (), witness.end ());
    if (!it.witness (clause, witness))
      return false;
    clause.clear ();
    witness.clear ();
  }
  return true;
}

bool External::traverse_witnesses_forward (WitnessIterator & it) {
  if (internal->unsat) return true;
  vector<int> clause, witness;
  const auto end = extension.end ();
  auto i = extension.begin ();
  if (i != end) {
    int lit = *i++;
    do {
      assert (!lit), (void) lit;
      while ((lit = *i++))
        witness.push_back (lit);
      assert (!lit);
      assert (i != end);
      while (i != end && (lit = *i++))
        clause.push_back (lit);
      if (!it.witness (clause, witness))
        return false;
      clause.clear ();
      witness.clear ();
    } while (i != end);
  }
  return true;
}

/*------------------------------------------------------------------------*/

}
