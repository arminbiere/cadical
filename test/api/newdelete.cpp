#include "../../src/cadical.hpp"
int main () {
  CaDiCaL::Solver *solver = new CaDiCaL::Solver ();
  delete solver;
  return 0;
}
