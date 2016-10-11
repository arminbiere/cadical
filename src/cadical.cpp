#include "cadical.hpp"
#include "internal.hpp"

namespace CaDiCaL {

Solver::Solver () { internal = new Internal (); }
Solver::~Solver () { delete internal; }

void Solver::statistics () { internal->stats.print (); }

};
