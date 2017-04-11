#include "../../src/ccadical.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

int main () {
  CCaDiCaL * solver = ccadical_init ();
  int res = ccadical_sat (solver);
  assert (res == 10);
  ccadical_add (solver, 1); ccadical_add (solver, 2); ccadical_add (solver, 0);
  ccadical_add (solver,-1); ccadical_add (solver, 2); ccadical_add (solver, 0);
  ccadical_add (solver, 1); ccadical_add (solver, -2); ccadical_add (solver, 0);
  res = ccadical_sat (solver);
  assert (res == 10);
  res = ccadical_deref (solver, 1);
  assert (res == 1);
  res = ccadical_deref (solver, 2);
  assert (res == 1);
  ccadical_reset (solver);
  return 0;
}
