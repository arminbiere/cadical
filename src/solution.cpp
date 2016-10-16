#include "internal.hpp"

namespace CaDiCaL {

// Sam Buss suggested to debug the case where a solver incorrectly claims the
// formula to be unsatisfiable by checking every learned clause to be satisfied by
// a satisfying assignment.  Thus the first inconsistent learned clause will be
// immediately flagged without the need to generate proof traces and perform
// forward proof checking.  The incorrectly derived clause will raise an abort
// signal and thus allows to debug the issue with a symbolic debugger immediately.

int Internal::sol (int lit) {
  assert (solution);
  int res = solution[vidx (lit)];
  if (lit < 0) res = -res;
  return res;
}

void Internal::check_clause () {
  if (!solution) return;
  bool satisfied = false;
  const const_int_iterator end = clause.end ();
  const_int_iterator i;
  for (const_int_iterator i = clause.begin (); !satisfied && i != end; i++)
    satisfied = (sol (*i) > 0);
  if (satisfied) return;
  fflush (stdout);
  fputs (
    "*** cadical error: learned clause unsatisfied by solution:\n",
    stderr);
  for (const_int_iterator i = clause.begin (); i != end; i++)
    fprintf (stderr, "%d ", *i);
  fputs ("0\n", stderr);
  fflush (stderr);
  abort ();
}

};
