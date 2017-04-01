#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

Internal::Internal ()
:
  unsat (false),
  iterating (false),
  clashing (false),
  simplifying (false),
  vivifying (false),
  vsize (0),
  max_var (0),
  level (0),
  vals (0),
  marks (0),
  phases (0),
  i2e (0),
  vtab (0),
  ltab (0),
  ftab (0),
  btab (0),
  otab (0),
  ntab (0),
  ntab2 (0),
  ptab (0),
  big (0),
  wtab (0),
  conflict (0),
  propagated (0),
  probagated (0),
  probagated2 (0),
  esched (more_noccs2 (this)),
  wg (0.5), ws (0.5),
  proof (0),
  opts (this),
#ifndef QUIET
  profiles (this),
#endif
  arena (this),
  output (File::write (this, stdout, "<stdou>")),
  internal (this),
  external (0)
{
  control.push_back (Level (0));
  binary_subsuming.redundant = false;
  binary_subsuming.size = 2;
}

Internal::~Internal () {
  for (clause_iterator i = clauses.begin (); i != clauses.end (); i++)
    delete_clause (*i);
  if (proof) delete proof;
  if (vtab) DELETE_ONLY (vtab, Var, vsize);
  if (ltab) DELETE_ONLY (ltab, Link, vsize);
  if (ftab) DELETE_ONLY (ftab, Flags, vsize);
  if (btab) DELETE_ONLY (btab, long, vsize);
  if (ptab) DELETE_ONLY (ptab, int, 2*vsize);
  if (big) RELEASE_DELETE (big, Bins, 2*vsize);
  if (vals) { vals -= vsize; DELETE_ONLY (vals, signed_char, 2*vsize); }
  if (marks) DELETE_ONLY (marks, signed_char, vsize);
  if (phases) DELETE_ONLY (phases, signed_char, vsize);
  if (i2e) DELETE_ONLY (i2e, int, vsize);
  if (otab) reset_occs ();
  if (ntab) reset_noccs ();
  if (ntab2) reset_noccs2 ();
  if (wtab) reset_watches ();
  delete output;
}

/*------------------------------------------------------------------------*/

void Internal::enlarge_vals (int new_vsize) {
  signed char * new_vals;
  NEW_ZERO (new_vals, signed_char, 2*new_vsize);
  new_vals += new_vsize;
  if (vals) memcpy (new_vals - max_var, vals - max_var, 2*max_var + 1);
  vals -= vsize;
  DELETE_ONLY (vals, signed_char, vsize);
  vals = new_vals;
}

void Internal::enlarge (int new_max_var) {
  size_t new_vsize = vsize ? 2*vsize : 1 + (size_t) new_max_var;
  while (new_vsize <= (size_t) new_max_var) new_vsize *= 2;
  LOG ("enlarge internal from size %ld to new size %ld", vsize, new_vsize);
  // Ordered in the size of allocated memory (larger block first).
  ENLARGE_ZERO (wtab, Watches, 2*vsize, 2*new_vsize);
  ENLARGE_ONLY (vtab, Var, vsize, new_vsize);
  ENLARGE_ONLY (ltab, Link, vsize, new_vsize);
  ENLARGE_ZERO (btab, long, vsize, new_vsize);
  ENLARGE_ONLY (ptab, int, 2*vsize, 2*new_vsize);
  ENLARGE_ONLY (i2e, int, vsize, new_vsize);
  enlarge_vals (new_vsize);
  ENLARGE_ONLY (phases, signed_char, vsize, new_vsize);
  ENLARGE_ZERO (marks, signed_char, vsize, new_vsize);
  ENLARGE_ONLY (ftab, Flags, vsize, new_vsize);
  assert (sizeof (Flags) == 1);
  vsize = new_vsize;
}

// Initialize VMTF queue from current 'max_var+1' to 'new_max_var'.  This
// incorporates an initial variable order.  We currently simply assume that
// variables with smaller index are more important.
//
void Internal::init_queue (int new_max_var) {
  int prev = queue.last;
  assert ((size_t) new_max_var < vsize);
  for (int i = new_max_var; i > max_var; i--) {
    Link * l = ltab + i;
    if ((l->prev = prev)) ltab[prev].next = i; else queue.first = i;
    btab[i] = ++stats.bumped;
    prev = i;
  }
  if (prev) ltab[prev].next = 0; else queue.first = 0;
  queue.bumped = btab[prev];
  queue.last = queue.unassigned = prev;
}

void Internal::init (int new_max_var) {
  if (new_max_var <= max_var) return;
  if ((size_t) new_max_var >= vsize) enlarge (new_max_var);
  signed char val = opts.phase ? 1 : -1;
  for (int i = max_var + 1; i <= new_max_var; i++) phases[i] = val;;
#ifndef NDEBUG
  for (int i = -new_max_var; i < -max_var; i++) assert (!vals[i]);
  for (int i = max_var + 1; i <= new_max_var; i++) assert (!vals[i]);
  for (int i = max_var + 1; i <= new_max_var; i++) assert (!marks[i]);
  for (int i = max_var + 1; i <= new_max_var; i++) assert (!btab[i]);
#endif
  for (int i = 2*(max_var + 1); i <= 2*new_max_var+1; i++) ptab[i] = -1;
  for (int i = max_var + 1; i <= new_max_var; i++) ftab[i].init ();
  assert (!btab[0]);
  init_queue (new_max_var);
  LOG ("initialized %d internal variables", new_max_var - max_var);
  max_var = new_max_var;
}

void Internal::add_original_lit (int lit) {
  assert (abs (lit) <= max_var);
  if (lit) clause.push_back (lit);
  else {
    if (!tautological_clause ()) add_new_original_clause ();
    else LOG ("tautological original clause");
    clause.clear ();
  }
}

/*------------------------------------------------------------------------*/

// This is the main CDCL loop with interleaved inprocessing.

int Internal::search () {
  int res = 0;
  START (search);
  while (!res)
         if (unsat) res = 20;
    else if (!propagate ()) analyze ();    // analyze propagated conflict
    else if (iterating) iterate ();        // report learned unit
    else if (satisfied ()) res = 10;       // all variables satisfied
    else if (terminating ()) break;        // limit hit or asynchronous abort
    else if (restarting ()) restart ();    // restart by backtracking
    else if (rephasing ()) rephase ();     // reset phases
    else if (reducing ()) reduce ();       // collect useless learned clauses
    else if (probing ()) probe ();         // failed literal probing
    else if (subsuming ()) subsume ();     // subsumption algorithm
    else if (eliminating ()) elim ();      // bounded variable elimination
    else if (compactifying ()) compact (); // collect internal variables
    else decide ();                        // otherwise pick next decision
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

  lim.removed_at_last_elim = -1;

  lim.elim = opts.eliminit;
  inc.elim = (opts.elimint + 1)/2;

  lim.probe = opts.probeinit;
  inc.probe = (opts.probeint + 1)/2;

  lim.compact = opts.compactint;
  inc.compact = opts.compactint;

  inc.rephase = opts.rephaseint;
  lim.rephase = opts.rephaseint;

  lim.conflict = (opts.clim < 0) ? -1 : stats.conflicts + opts.clim;
  lim.decision = (opts.dlim < 0) ? -1 : stats.decisions + opts.dlim;

  INIT_EMA (fast_glue_avg, opts.emagluefast);
  INIT_EMA (jump_avg, opts.emajump);
  INIT_EMA (size_avg, opts.emasize);
  INIT_EMA (slow_glue_avg, opts.emaglueslow);
}

int Internal::solve () {
  SECTION ("solving");
  int res;
  if (unsat) {
    LOG ("already inconsistent");
    res = 20;
  } else if (clashing) {                  // clashing original unit clauses
    LOG ("clashing original clause");
    learn_empty_clause ();
    res = 20;
  } else if (!propagate ()) {
    LOG ("root level propagation produces conflict");
    learn_empty_clause ();
    res = 20;
  } else {
    init_solving ();
    garbage_collection ();
    res = search ();
  }
  report ((res == 10) ? '1' : (res == 20 ? '0' : '?'));
  return res;
}

/*------------------------------------------------------------------------*/

void External::check (int (External::*a)(int) const) {

  // First check all assigned and 'vals[idx] == -vals[-idx]' consistency.
  //
  for (int idx = 1; idx <= max_var; idx++) {
    if (!(this->*a) (idx)) {
      fflush (stdout);
      fprintf (stderr,
        "*** cadical error: unassigned variable: %d\n", idx);
      fflush (stderr);
      abort ();
    }
    if ((this->*a) (idx) != -(this->*a)(-idx)) {
      fflush (stdout);
      fprintf (stderr,
        "*** cadical error: inconsistently assigned literals %d and %d\n",
        idx, -idx);
      fflush (stderr);
      abort ();
    }
  }

  // Then check that all (saved) original clauses are satisfied.
  //
  bool satisfied = false;
  const const_int_iterator end = original.end ();
  const_int_iterator start = original.begin ();
  for (const_int_iterator i = start; i != end; i++) {
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

#ifndef QUIET
  if (internal->opts.verbose) {
    MSG ("");
    MSG ("satisfying assignment checked");
    MSG ("");
  }
#endif
}

// Currently only used for debugging purposes.

void Internal::dump () {
  const const_clause_iterator eoc = clauses.end ();
  const_clause_iterator i;
  printf ("p cnf %d %ld\n", max_var, stats.irredundant + stats.redundant);
  for (i = clauses.begin (); i != eoc; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    const const_literal_iterator eol = c->end ();
    const_literal_iterator j = c->begin ();
    for (j = c->begin (); j != eol; j++)
      printf ("%d ", *j);
    printf ("0\n");
  }
  fflush (stdout);
}

};
