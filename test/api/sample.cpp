#include "../../src/cadical.hpp"
#ifdef NDEBUG
#undef NDEBUG
#endif
#include <cassert>

int main () {

  CaDiCaL::Solver solver;

  solver.set ("log", 1);
  solver.configure ("plain");
  solver.set ("randomdecision", 1);
  solver.set ("randomphase", 1);

  constexpr int n = 7;

  for (int i = 1; i <= n; i++)
    solver.add (i);
  solver.add (0);

  int prev[n + 1], values[n + 1];
  size_t models = 0, sum_distances = 0;

  while (solver.solve () == 10) {
    models++;
    for (int i = 1; i <= n; i++)
      values[i] = (solver.val (i) == i ? i : -i);
    unsigned distance = 0;
    if (models > 1) {
      for (int i = 1; i <= n; i++)
        if (values[i] != prev[i])
          distance++;
      sum_distances += distance;
    }
    for (int i = 1; i <= n; i++)
      prev[i] = values[i];
#if 1
    printf ("%zu", models);
    for (int i = 1; i <= n; i++)
      printf ("\t%d", values[i]);
    if (models > 1)
      printf ("\t%u", distance);
    fputc ('\n', stdout);
    fflush (stdout);
#endif
    for (int i = 1; i <= n; i++)
      solver.add (-values[i]);
    solver.add (0);
  }

  printf ("%.2f\n", sum_distances / (double) (models - 1));

  return 0;
}
