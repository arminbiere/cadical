#include "internal.hpp"
#include "external.hpp"
#include "message.hpp"
#include "macros.hpp"

namespace CaDiCaL {

// The extension stack allows to reconstruct an assignment for the original
// formula after removing eliminated clauses.  This was pioneered by Niklas
// Soerensson in MiniSAT and for instance is described in our inprocessing
// paper, published at IJCAR'12.  This first function adds a clause to this
// stack.  First the blocking or eliminated literal is added, and then the
// rest of the clause.

void External::push_on_extension_stack (Clause * c, int pivot) {
  extension.push_back (0);
  const const_literal_iterator end = c->end ();
  const_literal_iterator l;
  extension.push_back (pivot);
  for (l = c->begin (); l != end; l++)
    if (*l != pivot) extension.push_back (*l);
}

// This is the actual extension process. It goes backward over the clauses
// on the extension stack and flips the assignment of the last literal found
// in a clause if the clause is falsified.

void External::extend () {
  START (extend);
  long flipped = 0;
  VRB ("extend",
    "mapping internal %d assignments to %d assignments",
    internal->max_var, max_var);
  for (int i = 1; i <= max_var; i++)
    vals[i] = internal->val (internalize (i));
  VRB ("extend",
    "extending through extension stack of size %ld",
    (long) extension.size ());
  const const_int_iterator begin = extension.begin ();
  const_int_iterator i = extension.end ();
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
