#include "internal.hpp"

namespace CaDiCaL {

Internal::Internal ()
:
  max_var (0),
  vsize (0),
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
  internal (this)
{
  control.push_back (Level (0));
}

void Internal::resize (int new_max_var) {
  if (new_max_var < max_var) return;
  if ((size_t) new_max_var >= vsize) {
    size_t new_vsize = vsize ? 2*vsize : 1 + (size_t) new_max_var;
    while (new_vsize <= (size_t) new_max_var) new_vsize *= 2;
    vector<int> order;
    queue.save (this, order);
    RESIZE (vals,   signed char,   vsize,   new_vsize);
    RESIZE (phases, signed char,   vsize,   new_vsize);
    RESIZE (vtab,           Var,   vsize,   new_vsize);
    RESIZE (wtab,       Watches, 2*vsize, 2*new_vsize);
    queue.restore (this, order);
    vsize = new_vsize;
  }
  for (int i = max_var + 1; i <= new_max_var; i++) vals[i] = 0;
  for (int i = max_var + 1; i <= new_max_var; i++) phases[i] = -1;
  queue.init (this, new_max_var);
  MSG ("initialized %d variables", new_max_var - max_var);
}

Internal::~Internal () {
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

int Internal::search () {
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

void Internal::init_solving () {
  restart_limit = opts.restartint;
  reduce_limit = reduce_inc = opts.reduceinit;
  INIT_EMA (fast_glue_avg, opts.emagluefast);
  INIT_EMA (slow_glue_avg, opts.emaglueslow);
}

int Internal::solve () {
  init_solving ();
  SECTION ("solving");
  if (clashing_unit) { learn_empty_clause (); return 20; }
  else return search ();
}

/*------------------------------------------------------------------------*/

void Internal::check (int (Internal::*a)(int)) {
  bool satisfied = false;
  size_t start = 0;
  for (size_t i = 0; i < original.size (); i++) {
    int lit = original[i];
    if (!lit) {
      if (!satisfied) {
        fflush (stdout);
        fputs ("*** cadical error: unsatisfied clause:\n", stderr);
        for (size_t j = start; j < i; j++)
          fprintf (stderr, "%d ", original[j]);
        fputs ("0\n", stderr);
        fflush (stderr);
        abort ();
      }
      satisfied = false;
      start = i + 1;
    } else if (!satisfied && (this->*a) (lit) > 0) satisfied = true;
  }
  MSG ("satisfying assignment checked");
}

};
