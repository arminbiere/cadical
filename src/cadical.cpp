#include "cadical.hpp"

#include <cstring>

namespace CaDiCaL {

Solver::Solver ()
: 
  max_var (0),
  num_original_clauses (0),
  vars (0),
  vals (0),
  phases (0),
  unsat (false),
  level (0),
  conflict (0),
  clashing_unit (false),
  solution (0),
  proof (0),
  opts (this),
  stats (this)
{
  literal.watches = 0;
  literal.binaries = 0;
  next.binaries = 0;
  next.watches = 0;
  iterating = false;
  blocking.enabled = false;
  blocking.exploring = false;
  memset (&limits, 0, sizeof limits);
  memset (&inc, 0, sizeof limits);
}

};
