#include "../../src/cadical.hpp"

#ifdef NDEBUG
#undef NDEBUG
#endif

extern "C" {
#include <assert.h>
#include <signal.h>
#include <unistd.h>
}

static int n = 10;

static int ph (int p, int h) {
  assert (0 <= p), assert (p < n + 1);
  assert (0 <= h), assert (h < n);
  return 1 + h * (n + 1) + p;
}

static CaDiCaL::Solver solver, solver2;

int main () {
  solver.set ("factor", 1);
  solver.set ("preprocesslight", 1);
  solver.limit ("conflicts", 1000);
  // resize to the highest possible number
  solver.resize (ph (n, n - 1));

  // Construct a pigeon hole formula for 'n+1' pigeons in 'n' holes.
  //
  for (int h = 0; h < n; h++)
    for (int p1 = 0; p1 < n + 1; p1++)
      for (int p2 = p1 + 1; p2 < n + 1; p2++)
        solver.add (-ph (p1, h)), solver.add (-ph (p2, h)), solver.add (0);

  for (int p = 0; p < n + 1; p++) {
    for (int h = 0; h < n; h++)
      solver.add (ph (p, h));
    solver.add (0);
  }

  int res = solver.solve ();
  solver.statistics ();
  assert (!res);
  solver.copy (solver2);
  res = solver2.solve ();
  assert (res == 20);

  solver2.statistics ();

  return 0;
}
