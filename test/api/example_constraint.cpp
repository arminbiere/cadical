#include "../../src/cadical.hpp"
#ifdef NDEBUG
#undef NDEBUG
#endif
#include <cassert>

// This is the example from the header file

int main () {

  CaDiCaL::Solver *solver = new CaDiCaL::Solver;

  // ------------------------------------------------------------------
  // Encode Problem and check without assumptions.

  enum { TIE = 1, SHIRT = 2 };

  solver->add (-TIE), solver->add (SHIRT), solver->add (0);
  solver->add (TIE), solver->add (SHIRT), solver->add (0);
  solver->add (-TIE), solver->add (-SHIRT), solver->add (0);

  int res = solver->solve (); // Solve instance.
  assert (res == 10);         // Check it is 'SATISFIABLE'.

  res = solver->val (TIE); // Obtain assignment of 'TIE'.
  assert (res < 0);        // Check 'TIE' assigned to 'false'.

  res = solver->val (SHIRT); // Obtain assignment of 'SHIRT'.
  assert (res > 0);          // Check 'SHIRT' assigned to 'true'.

  // ------------------------------------------------------------------
  // Incrementally solve again under one assumption.

  solver->assume (TIE); // Now force 'TIE' to true.

  res = solver->solve (); // Solve again incrementally.
  assert (res == 20);     // Check it is 'UNSATISFIABLE'.

  res = solver->failed (TIE); // Check 'TIE' responsible.
  assert (res);               // Yes, 'TIE' in core.

  res = solver->failed (SHIRT); // Check 'SHIRT' responsible.
  assert (!res);                // No, 'SHIRT' not in core.

  // ------------------------------------------------------------------
  // Incrementally solve with constraint.

  solver->constrain (TIE), solver->constrain (-SHIRT),
      solver->constrain (0);

  res = solver->solve (); // Solve again incrementally.
  assert (res == 20);     // Check it is 'UNSATISFIABLE'.

  res = solver->constraint_failed (); // Check constraint responsible.
  assert (res);                       // Yes, constraint was used.

  // ------------------------------------------------------------------
  // Incrementally solve once more under another assumption.

  solver->assume (-SHIRT); // Now force 'SHIRT' to false.

  res = solver->solve (); // Solve again incrementally.
  assert (res == 20);     // Check it is 'UNSATISFIABLE'.

  res = solver->failed (TIE); // Check 'TIE' responsible.
  assert (!res);              // No, 'TIE' not in core.

  res = solver->failed (-SHIRT); // Check '!SHIRT' responsible.
  assert (res);                  // Yes, '!SHIRT' in core.

  // ------------------------------------------------------------------

  delete solver;

  return 0;
}
