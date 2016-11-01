#include "internal.hpp"

#include "iterator.hpp"
#include "macros.hpp"
#include "message.hpp"
#include "clause.hpp"
#include "proof.hpp"

namespace CaDiCaL {

Internal::Internal ()
:
  unsat (false),
  iterating (false),
  clashing (false),
  vsize (0),
  maxvar (0),
  level (0),
  vals (0),
  solution (0),
  marks (0),
  phases (0),
  vtab (0),
  ltab (0),
  ftab (0),
  btab (0),
  wtab (0),
  conflict (0),
  propagated (0),
  proof (0),
  opts (this),
  profiles (this),
  arena (this),
  internal (this)
{
  control.push_back (Level (0));
  inc_bytes (sizeof *this);
}

Internal::~Internal () {
  for (clause_iterator i = clauses.begin (); i != clauses.end (); i++)
    delete_clause (*i);
  if (proof) delete proof;
  if (wtab) delete [] wtab;
  if (vtab) delete [] vtab;
  if (ltab) delete [] ltab;
  if (ftab) delete [] ftab;
  if (btab) delete [] btab;
  if (vals) vals -= vsize, delete [] vals;
  if (solution) solution -= vsize, delete [] solution;
  if (marks) delete [] marks;
  if (phases) delete [] phases;
}

/*------------------------------------------------------------------------*/

void Internal::enlarge_vals (int new_vsize) {
  signed char * new_vals;
  NEW (new_vals, signed char, 2*new_vsize);
  new_vals += new_vsize;
  if (vals) memcpy (new_vals - maxvar, vals - maxvar, 2*maxvar + 1);
  dec_bytes (2*vsize * sizeof *vals);
  vals -= vsize;
  delete [] vals;
  vals = new_vals;
}

void Internal::enlarge (int new_maxvar) {
  size_t new_vsize = vsize ? 2*vsize : 1 + (size_t) new_maxvar;
  while (new_vsize <= (size_t) new_maxvar) new_vsize *= 2;
  ENLARGE (vtab, Var, vsize, new_vsize);
  ENLARGE (ltab, Link, vsize, new_vsize);
  ENLARGE (marks, signed char, vsize, new_vsize);
  ENLARGE (phases, signed char, vsize, new_vsize);
  ENLARGE (wtab, Watches, 2*vsize, 2*new_vsize);
  ENLARGE (ftab, Flags, vsize, new_vsize);
  ENLARGE (btab, long, vsize, new_vsize);
  assert (sizeof (Flags) == 1);
  enlarge_vals (new_vsize);
  vsize = new_vsize;
}

// Initialize VMTF queue from current 'maxvar+1' to 'new_maxvar'.  This
// incorporates an initial variable order.  We currently simply assume that
// variables with smaller index are more important.
//
void Internal::resize_queue (int new_maxvar) {
  int prev = queue.last;
  assert ((size_t) new_maxvar < vsize);
  for (int i = new_maxvar; i > maxvar; i--) {
    Link * l = ltab + i;
    if ((l->prev = prev)) ltab[prev].next = i; else queue.first = i;
    btab[i] = ++stats.bumped;
    prev = i;
  }
  if (prev) ltab[prev].next = 0; else queue.first = 0;
  queue.bumped = btab[prev];
  queue.last = queue.unassigned = prev;
}

void Internal::resize (int new_maxvar) {
  if (new_maxvar < maxvar) return;
  if ((size_t) new_maxvar >= vsize) enlarge (new_maxvar);
  for (int i = -new_maxvar; i < -maxvar; i++) vals[i] = 0;
  for (int i = maxvar + 1; i <= new_maxvar; i++) vals[i] = 0;
  for (int i = maxvar + 1; i <= new_maxvar; i++) phases[i] = -1;
  for (int i = maxvar + 1; i <= new_maxvar; i++) marks[i] = 0;
  for (int i = maxvar + 1; i <= new_maxvar; i++) btab[i] = 0;
  if (!maxvar) btab[0] = 0;
  resize_queue (new_maxvar);
  MSG ("initialized %d variables", new_maxvar - maxvar);
  maxvar = new_maxvar;
}

void Internal::add_original_lit (int lit) {
  assert (abs (lit) <= maxvar);
  if (opts.check) original.push_back (lit);
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
    else if (terminating ()) break;
    else if (restarting ()) restart ();
    else if (reducing ()) reduce ();
    else if (subsuming ()) subsume ();
    else decide ();
  STOP (search);
  return res;
}

/*------------------------------------------------------------------------*/

void Internal::init_solving () {

  lim.restart = opts.restartint;

  lim.reduce  = opts.reduceinit;
  inc.reduce  = opts.reduceinit;
  inc.redinc  = opts.reduceinc;

  lim.subsume = opts.subsumeinit;
  inc.subsume = opts.subsumeinit;

  lim.conflict = (opts.clim < 0) ? -1 : stats.conflicts + opts.clim;
  lim.decision = (opts.dlim < 0) ? -1 : stats.decisions + opts.dlim;

  INIT_EMA (fast_glue_avg, opts.emagluefast);
  INIT_EMA (jump_avg, opts.emajump);
  INIT_EMA (restarteff, opts.emarestarteff);
  INIT_EMA (restartint, opts.emarestartint);
  INIT_EMA (size_avg, opts.emasize);
  INIT_EMA (slow_glue_avg, opts.emaglueslow);
}

int Internal::solve () {
  init_solving ();
  SECTION ("solving");
  int res;
  if (clashing) {                  // clashing original unit clauses
    learn_empty_clause ();
    res = 20;
  } else {
    res = search ();
    if (res == 10) check (&Internal::val);
  }
  report ((res == 10) ? '1' : (res == 20 ? '0' : '?'));
  return res;
}

/*------------------------------------------------------------------------*/

void Internal::check (int (Internal::*a)(int) const) {
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
  if (opts.verbose) {
    MSG ("");
    MSG ("satisfying assignment checked");
    MSG ("");
  }
}

};
