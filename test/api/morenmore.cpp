#include "../../src/cadical.hpp"
#include <cassert>
#include <iostream>
using namespace std;
int main () {
  CaDiCaL::Solver solver;
  const int n = 100;
  for (int i = 1; i < n; i++) {
    for (int j = 1; j < i; j++)
      solver.add (-j);
    solver.add (i), solver.add (0);
  }
  int res = solver.solve ();
  assert (res == 10);
  for (int i = 1; i < n; i++) {
    res = solver.val (i);
    assert (res > 0);
  }
  (void) res;
  return 0;
}
