#include "internal.hpp"

namespace CaDiCaL {

// The extension stack allows to reconstruct an assignment for the original
// formula after removing eliminated clauses.  This was pioneered by Niklas
// Soerensson in MiniSAT and for instance is described in our inprocessing
// paper, published at IJCAR'12.  This first function adds a clause to this
// stack.  First the blocking or eliminated literal is added, and then the
// rest of the clause.

void External::push_unit_on_extension_stack (int pivot) {
  extension.push_back (0);
  LOG ("pushing 0 on extension stack");
  const int epivot = internal->externalize (pivot);
  assert (epivot);
  extension.push_back (epivot);
  LOG ("pushing pivot %d on extension stack (internal %d)", epivot, pivot);
}

void External::push_clause_on_extension_stack (Clause * c, int pivot) {
  push_unit_on_extension_stack (pivot);
  const const_literal_iterator end = c->end ();
  const_literal_iterator l;
  for (l = c->begin (); l != end; l++) {
    const int lit = *l;
    if (lit == pivot) continue;
    const int elit = internal->externalize (lit);
    assert (elit);
    extension.push_back (elit);
    LOG ("pushing %d on extension stack (internal %d)",
      elit, lit);
  }
}

void External::push_binary_on_extension_stack (int pivot, int other) {
  push_unit_on_extension_stack (pivot);
  const int eother = internal->externalize (other);
  assert (other);
  extension.push_back (eother);
  LOG ("pushing %d on extension stack (internal %d)",
    eother, other);
}

// This is the actual extension process. It goes backward over the clauses
// on the extension stack and flips the assignment of the last literal found
// in a clause if the clause is falsified.

void External::extend () {
  START (extend);
  VRB ("extend",
    "mapping internal %d assignments to %d assignments",
    internal->max_var, max_var);
  long updated = 0;
  for (int i = 1; i <= max_var; i++) {
    const int ilit = e2i[i];
    if (!ilit) continue;
    vals[i] = internal->val (ilit);
    updated++;
  }
  VRB ("extend", "updated %ld external assignments", updated);
  VRB ("extend",
    "extending through extension stack of size %ld",
    (long) extension.size ());
  const const_int_iterator begin = extension.begin ();
  const_int_iterator i = extension.end ();
  long flipped = 0;
  while (i != begin) {
    bool satisfied = false;
    int lit, last = 0;
    assert (i != begin);
    while ((lit = *--i)) {
      if (satisfied) continue;
      if (val (lit) > 0) satisfied = true;
      assert (i != begin);
      last = lit;
    }
    if (satisfied) continue;
    assert (last);
    LOG ("flipping blocking literal %d", last);
    vals[vidx (last)] = sign (last);
    flipped++;
  }
  VRB ("extend", "flipped %ld literals during extension", flipped);
  STOP (extend);
}

};
