#include "../../src/ccadical.h"
// #include <sys/resource.h>

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

#define BIG_NUM 100000

int main (void) {
  // At the start of main():
  // struct rlimit core_limit = {0, 0};
  // setrlimit (RLIMIT_CORE, &core_limit);

  struct CCaDiCaL *solver = ccadical_init ();
  ccadical_set_option (solver, "verbose", 3);
  ccadical_set_option (solver, "ilb", 2);
  ccadical_set_option (solver, "elevate", 2);
  ccadical_set_option (solver, "factor", 0);
  ccadical_set_option (solver, "factorcheck", 0);
  // ccadical_set_option (solver, "log", 1);
  for (int i = 2; i < BIG_NUM; i++) {
    ccadical_add (solver, i - 1);
    ccadical_add (solver, i);
    ccadical_add (solver, 0);
  }
  int res = ccadical_solve (solver);
  assert (res == 10);
  for (int i = 1; i < BIG_NUM; i++) {
    assert (ccadical_val (solver, i) == i);
  }
  for (int i = 2; i < BIG_NUM; i++) {
    if (__builtin_popcount (i) == 1)
      printf ("iteration %d\n", i);
    ccadical_add (solver, (i));
    // ccadical_add (solver, -(i));
    // ccadical_add (solver, 0);
    // ccadical_add (solver, -(i - 1));
    // ccadical_add (solver, (i));
    ccadical_add (solver, 0);
    int res = ccadical_solve (solver);
    assert (res == 10);
  }
  ccadical_release (solver);
  return 0;
}
