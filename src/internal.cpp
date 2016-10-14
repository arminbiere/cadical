#include "internal.hpp"

#include "iterator.hpp"
#include "macros.hpp"
#include "message.hpp"
#include "proof.hpp"

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
  solution (0),
  profiles (this),
  internal (this)
{
  control.push_back (Level (0));
}

Internal::~Internal () {
  for (clause_iterator i = clauses.begin (); i != clauses.end (); i++)
    delete_clause (*i);
  if (proof) delete proof;
  if (wtab) delete [] wtab;
  if (vtab) delete [] vtab;
  if (vals) delete [] vals;
  if (phases) delete [] phases;
  if (solution) delete [] solution;
}

/*------------------------------------------------------------------------*/

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
  max_var = new_max_var;
}

void Internal::add_original_lit (int lit) {
  assert (abs (lit) <= max_var);
  original.push_back (lit);
  if (lit) clause.push_back (lit);
  else {
    if (!tautological_clause ()) add_new_original_clause ();
    else LOG ("tautological original clause");
    clause.clear ();
  }
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
  int res = search ();
  if (res == 10) check (&Internal::val);
  return res;
}

/*------------------------------------------------------------------------*/

void Internal::check (int (Internal::*a)(int)) {
  bool satisfied = false;
  const_int_iterator start = original.begin ();
  for (const_int_iterator i = start; i != original.end (); i++) {
    int lit = *i;
    if (!lit) {
      if (!satisfied) {
        fflush (stdout);
        fputs ("*** cadical error: unsatisfied clause:\n", stderr);
        for (const_int_iterator j = start; j != i; j++)
          fprintf (stderr, "%d ", *j);
        fputs ("0\n", stderr);
        fflush (stderr);
        abort ();
      }
      satisfied = false;
      start = i + 1;
    } else if (!satisfied && (this->*a) (lit) > 0) satisfied = true;
  }
  if (internal->opts.verbose) {
    MSG ("");
    MSG ("satisfying assignment checked");
    MSG ("");
  }
}

};
