#ifndef _cadical_hpp_INCLUDED
#define _cadical_hpp_INCLUDED

#include <vector>

#include <climits>
#include <cassert>

#include "options.hpp"
#include "clause.hpp"
#include "var.hpp"
#include "watch.hpp"
#include "ema.hpp"
#include "avg.hpp"
#include "timer.hpp"

namespace CaDiCaL {

using namespace std;

class Solver {
  Options opts;
};

};

#endif
