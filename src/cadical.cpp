#include "cadical.hpp"
#include "internal.hpp"

namespace CaDiCaL {

Solver::Solver () { internal = new Internal (); }
Solver::~Solver () { delete internal; }

};
