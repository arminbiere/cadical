#include "../../src/cadical.hpp"
#include <iostream>
#include <cassert>
using namespace std;
int main () {
  CaDiCaL::Solver * solver = new CaDiCaL::Solver ();
  solver->add (1);
  solver->add (0);
  int res = solver->solve ();
  cout << "solver->solve () = " << res << endl << flush;
  assert (res == 10);
  res = solver->val (1);
  cout << "solver->val (1) = " << res << endl << flush;
  assert (res > 1);
  delete solver;
  return 0;
}
