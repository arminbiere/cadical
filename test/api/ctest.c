#include "../../src/ccadical.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

int main () {
  CCaDiCaL * solver = ccadical_init ();
  ccadical_set_option (solver, "log", 1);
  ccadical_set_option (solver, "verbose", 2);
  int res = ccadical_solve (solver);
  assert (res == 10);
  ccadical_add (solver, 1); ccadical_add (solver, 2); ccadical_add (solver, 0);
  ccadical_add (solver,-1); ccadical_add (solver, 2); ccadical_add (solver, 0);
  ccadical_add (solver, 1); ccadical_add (solver, -2); ccadical_add (solver, 0);
  res = ccadical_solve (solver);
  assert (res == 10);
  res = ccadical_val (solver, 1);
  assert (res == 1);
  res = ccadical_val (solver, 2);
  assert (res == 1);
  ccadical_release (solver);
  return 0;
}
