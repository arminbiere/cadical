#include "../../src/cadical.hpp"
#include <iostream>
#ifdef NDEBUG
#undef NDEBUG
#endif
#include <cassert>
using namespace std;
int main () {
  CaDiCaL::Solver solver;
  solver.add (1);
  solver.add (0);
  int res = solver.solve ();
  cout << "solver.solve () = " << res << endl << flush;
  assert (res == 10);
  res = solver.val (1);
  cout << "solver.val (1) = " << res << endl << flush;
  cout << "solver.val (-1) = " << solver.val (-1) << endl << flush;
  cout << "solver.val (2) = " << solver.val (2) << endl << flush;
  cout << "solver.val (3) = " << solver.val (3) << endl << flush;
  assert (res > 0);
  return 0;
}
