#include "solver.hpp"

#include <cstring>
#include <algorithm>

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
  proof (0),
  opts (this),
  stats (this),
#ifndef NDEBUG
  solution (0),
#endif
  solver (this)
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

/*------------------------------------------------------------------------*/

int Solver::search () {
  int res = 0;
  START (search);
  while (!res)
         if (unsat) res = 20;
    else if (!propagate ()) analyze ();
    else if (iterating) iterate ();
    else if (satisfied ()) res = 10;
    else if (restarting ()) restart ();
    else if (reducing ()) reduce ();
    else decide ();
  STOP (search);
  return res;
}

/*------------------------------------------------------------------------*/

void Solver::init_solving () {
  limits.restart.conflicts = opts.restartint;
  limits.reduce.conflicts = opts.reduceinit;
  inc.reduce = opts.reduceinit;
  inc.unit = opts.emaf1 ? 1.0 / opts.emaf1 : 1e-9;
  INIT_EMA (avg.glue.fast, opts.emagluefast);
  INIT_EMA (avg.frequency.unit, opts.emaf1);
  INIT_EMA (avg.trail, opts.ematrail);
  limits.blocking = inc.blocking = opts.restartblocklimit;
}

int Solver::solve () {
  init_solving ();
  SECTION ("solving");
  if (clashing_unit) { learn_empty_clause (); return 20; }
  else return search ();
}

};
