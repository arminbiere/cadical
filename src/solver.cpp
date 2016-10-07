#include "solver.hpp"

namespace CaDiCaL {

Solver::Solver ()
:
  max_var (0),
  vtab (0),
  vals (0),
  phases (0),
  wtab (0),
  unsat (false),
  level (0),
  propagated (0),
  iterating (false),
  conflict (0),
  clashing_unit (false),
  reduce_limit (0),
  restart_limit (0),
  recently_resolved (0),
  fixed_limit (0),
  reduce_inc (0),
  proof (0),
  opts (this),
  stats (this),
  solution (0),
  profiles (this),
  solver (this)
{
}

void Solver::init_variables () {
  const int max_lit = 2*max_var + 1;
  NEW (vals,   signed char, max_var + 1);
  NEW (phases, signed char, max_var + 1);
  NEW (vtab,           Var, max_var + 1);
  NEW (wtab,       Watches, max_lit + 1);
  for (int i = 1; i <= max_var; i++) vals[i] = 0;
  for (int i = 1; i <= max_var; i++) phases[i] = -1;
  queue.init (this);
  MSG ("initialized %d variables", max_var);
  control.push_back (Level (0));
}

Solver::~Solver () {
  for (size_t i = 0; i < clauses.size (); i++)
    delete_clause (clauses[i]);
  if (proof) delete proof;
  if (wtab) delete [] wtab;
  if (vtab) delete [] vtab;
  if (vals) delete [] vals;
  if (phases) delete [] phases;
  if (solution) delete [] solution;
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
  restart_limit = opts.restartint;
  reduce_limit = reduce_inc = opts.reduceinit;
  INIT_EMA (fast_glue_avg, opts.emagluefast);
  INIT_EMA (slow_glue_avg, opts.emaglueslow);
}

int Solver::solve () {
  init_solving ();
  SECTION ("solving");
  if (clashing_unit) { learn_empty_clause (); return 20; }
  else return search ();
}

};
