#include "cadical.hpp"

using namespace CaDiCaL;

extern "C" {

#include "ccadical.h"

CCaDiCaL * ccadical_init () { return (CCaDiCaL*) new Solver (); }
void ccadical_reset (CCaDiCaL * solver) { delete (Solver*) solver; }

void ccadical_add (CCaDiCaL * solver, int lit) {
  ((Solver*) solver)->add (lit);
}

int ccadical_sat (CCaDiCaL * solver) {
  return ((Solver*) solver)->solve ();
}

int ccadical_deref (CCaDiCaL * solver, int lit) {
  return ((Solver*) solver)->val (lit);
}

};

