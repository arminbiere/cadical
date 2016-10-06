#include "solver.hpp"

namespace CaDiCaL {

void AVG::update (Solver * solver, double y, const char * name) {
  value = count * value + y;
  value /= ++count;
  LOG ("update %s AVG with %g yields %g", name, y, value);
}

};
