#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

Internal::Internal ()
:
  mode (SEARCH),
  unsat (false),
  iterating (false),
  localsearching (false),
  preprocessing (false),
  force_saved_phase (false),
  termination_forced (false),
  searching_lucky_phases (false),
  stable (false),
  reported (false),
  rephased (0),
  vsize (0),
  max_var (0),
  level (0),
  vals (0),
  marks (0),
  frozentab (0),
  i2e (0),
  scinc (1.0),
  scores (this),
  stab (0),
  vtab (0),
  ltab (0),
  ftab (0),
  btab (0),
  otab (0),
  ptab (0),
  ntab (0),
  ntab2 (0),
  big (0),
  wtab (0),
  conflict (0),
  ignore (0),
  propagated (0),
  propagated2 (0),
  best_assigned (0),
  target_assigned (0),
  no_conflict_until (0),
  proof (0),
  checker (0),
  tracer (0),
  opts (this),
#ifndef QUIET
  profiles (this),
  force_phase_messages (false),
#endif
  arena (this),
  prefix ("c "),
  internal (this),
  external (0)
{
  control.push_back (Level (0, 0));
  binary_subsuming.redundant = false;
  binary_subsuming.size = 2;
}

Internal::~Internal () {
  for (const auto & c : clauses)
    delete_clause (c);
  if (proof) delete proof;
  if (tracer) delete tracer;
  if (checker) delete checker;
  if (vtab) DELETE_ONLY (vtab, Var, vsize);
  if (ltab) DELETE_ONLY (ltab, Link, vsize);
  if (ftab) DELETE_ONLY (ftab, Flags, vsize);
  if (btab) DELETE_ONLY (btab, long, vsize);
  if (stab) DELETE_ONLY (stab, double, vsize);
  if (ptab) DELETE_ONLY (ptab, int, 2*vsize);
  if (big) RELEASE_DELETE (big, Bins, 2*vsize);
  if (vals) { vals -= vsize; DELETE_ONLY (vals, signed_char, 2*vsize); }
  if (marks) DELETE_ONLY (marks, signed_char, vsize);
  if (phases.saved) DELETE_ONLY (phases.saved, Phase, vsize);
  if (phases.target) DELETE_ONLY (phases.target, Phase, vsize);
  if (phases.best) DELETE_ONLY (phases.best, Phase, vsize);
  if (phases.prev) DELETE_ONLY (phases.prev, Phase, vsize);
  if (phases.min) DELETE_ONLY (phases.min, Phase, vsize);
  if (i2e) DELETE_ONLY (i2e, int, vsize);
  if (frozentab) DELETE_ONLY (frozentab, unsigned, vsize);
  if (otab) reset_occs ();
  if (ntab) reset_noccs ();
  if (wtab) reset_watches ();
}

/*------------------------------------------------------------------------*/

void Internal::enlarge_vals (size_t new_vsize) {
  signed_char * new_vals;
  NEW_ZERO (new_vals, signed_char, 2*new_vsize);
  new_vals += new_vsize;
  if (vals) memcpy (new_vals - max_var, vals - max_var, 2*max_var + 1);
  vals -= vsize;
  DELETE_ONLY (vals, signed_char, 2*vsize);
  vals = new_vals;
}

void Internal::enlarge (int new_max_var) {
  assert (!level);
  size_t new_vsize = vsize ? 2*vsize : 1 + (size_t) new_max_var;
  while (new_vsize <= (size_t) new_max_var) new_vsize *= 2;
  LOG ("enlarge internal size from %ld to new size %ld", vsize, new_vsize);
  // Ordered in the size of allocated memory (larger block first).
  assert (!vsize || !otab);
  if (!vsize || wtab)
  ENLARGE_ZERO (wtab, Watches, 2*vsize, 2*new_vsize);
  ENLARGE_ONLY (vtab, Var, vsize, new_vsize);
  ENLARGE_ONLY (ltab, Link, vsize, new_vsize);
  ENLARGE_ZERO (btab, long, vsize, new_vsize);
  ENLARGE_ZERO (stab, double, vsize, new_vsize);
  ENLARGE_ONLY (ptab, int, 2*vsize, 2*new_vsize);
  ENLARGE_ONLY (i2e, int, vsize, new_vsize);
  enlarge_vals (new_vsize);
  ENLARGE_ZERO (frozentab, unsigned, vsize, new_vsize);
  ENLARGE_ONLY (phases.saved, Phase, vsize, new_vsize);
  ENLARGE_ZERO (phases.target, Phase, vsize, new_vsize);
  ENLARGE_ZERO (phases.best, Phase, vsize, new_vsize);
  ENLARGE_ZERO (phases.prev, Phase, vsize, new_vsize);
  ENLARGE_ZERO (phases.min, Phase, vsize, new_vsize);
  ENLARGE_ZERO (marks, signed_char, vsize, new_vsize);
  ENLARGE_ONLY (ftab, Flags, vsize, new_vsize);
  vsize = new_vsize;
}

void Internal::init (int new_max_var) {
  if (new_max_var <= max_var) return;
  if (level) backtrack ();
  LOG ("initializing %d internal variables from %d to %d",
    new_max_var - max_var, max_var + 1, new_max_var);
  if ((size_t) new_max_var >= vsize) enlarge (new_max_var);
  signed_char val = opts.phase ? 1 : -1;
  for (int i = max_var + 1; i <= new_max_var; i++)
    phases.saved[i] = val;
#ifndef NDEBUG
  for (int i = -new_max_var; i < -max_var; i++) assert (!vals[i]);
  for (int i = max_var + 1; i <= new_max_var; i++) assert (!vals[i]);
  for (int i = max_var + 1; i <= new_max_var; i++) assert (!frozentab[i]);
  for (int i = max_var + 1; i <= new_max_var; i++) assert (!marks[i]);
  for (int i = max_var + 1; i <= new_max_var; i++) assert (!btab[i]);
#endif
  for (int i = 2*(max_var + 1); i <= 2*new_max_var+1; i++) ptab[i] = -1;
  for (int i = max_var + 1; i <= new_max_var; i++) ftab[i].init ();
  assert (!btab[0]);
  int old_max_var = max_var;
  max_var = new_max_var;
  init_queue (old_max_var, new_max_var);
  init_scores (old_max_var, new_max_var);
  int initialized = new_max_var - old_max_var;
  stats.vars += initialized;
  stats.unused += initialized;
  stats.inactive += initialized;
  LOG ("finished initializing %d internal variables", initialized);
}

void Internal::add_original_lit (int lit) {
  assert (abs (lit) <= max_var);
  if (lit) {
    original.push_back (lit);
  } else {
    if (proof) proof->add_original_clause (original);
    add_new_original_clause ();
    original.clear ();
  }
}

/*------------------------------------------------------------------------*/

// This is the main CDCL loop with interleaved inprocessing.

int Internal::cdcl_loop_with_inprocessing () {

  int res = 0;

  START (search);

  if (stable) { START (stable);   report ('['); }
  else        { START (unstable); report ('{'); }

  while (!res) {
         if (unsat) res = 20;
    else if (!propagate ()) analyze ();      // propagate and analyze
    else if (iterating) iterate ();          // report learned unit
    else if (satisfied ()) res = 10;         // found model
    else if (terminating ()) break;          // limit hit or sync abort
    else if (restarting ()) restart ();      // restart by backtracking
    else if (rephasing ()) rephase ();       // reset variable phases
    else if (reducing ()) reduce ();         // collect useless clauses
    else if (probing ()) probe ();           // failed literal probing
    else if (subsuming ()) subsume ();       // subsumption algorithm
    else if (eliminating ()) elim ();        // variable elimination
    else if (compacting ()) compact ();      // collect variables
    else res = decide ();                    // next decision
  }

  if (stable) { STOP (stable);   report (']'); }
  else        { STOP (unstable); report ('}'); }

  STOP (search);

  return res;
}

/*------------------------------------------------------------------------*/

void Internal::init_limits () {

  const bool incremental = lim.initialized;
  if (incremental) LOG ("reinitializing limits incrementally");
  else LOG ("initializing limits and increments");

  const char * mode = 0;

  if (incremental) mode = "keeping";
  else {
    last.reduce.conflicts = -1;
    lim.reduce = stats.conflicts + opts.reduceint;
    mode = "initial";
  }
  (void) mode;
  LOG ("%s reduce limit %ld after %ld conflicts",
    mode, lim.reduce, lim.reduce - stats.conflicts);

  if (incremental) mode = "keeping";
  else {
    lim.flush = opts.flushint;
    inc.flush = opts.flushint;
    mode = "initial";
  }
  (void) mode;
  LOG ("%s flush limit %ld interval %ld",
    mode, lim.flush, inc.flush);

  if (incremental) mode = "keeping";
  else {
    lim.subsume = stats.conflicts + scale (opts.subsumeint);
    mode = "initial";
  }
  (void) mode;
  LOG ("%s subsume limit %ld after %ld conflicts",
    mode, lim.subsume, lim.subsume - stats.conflicts);

  if (incremental) mode = "keeping";
  else {
    last.elim.marked = -1;
    lim.elim = stats.conflicts + scale (opts.elimint);
    mode = "initial";
  }
  (void) mode;
  LOG ("%s elim limit %ld after %ld conflicts",
    mode, lim.elim, lim.elim - stats.conflicts);

  lim.elimbound = opts.elimboundmin;
  LOG ("elimination bound %ld", lim.elimbound);

  if (incremental) mode = "keeping";
  else {
    lim.probe = stats.conflicts + opts.probeint;
    mode = "initial";
  }
  (void) mode;
  LOG ("%s probe limit %ld after %ld conflicts",
    mode, lim.probe, lim.probe - stats.conflicts);

  if (!incremental) {

    last.ternary.marked = -1;

    lim.compact = stats.conflicts + opts.compactint;
    LOG ("initial compact limit %ld increment %ld",
      lim.compact, lim.compact - stats.conflicts);
  }

  lim.rephase = stats.conflicts + opts.rephaseint;
  lim.rephased[0] = lim.rephased[1] = 0;
  LOG ("new rephase limit %ld after %ld conflicts",
    lim.rephase, lim.rephase - stats.conflicts);

  lim.restart = stats.conflicts + opts.restartint;
  LOG ("new restart limit %ld increment %ld",
    lim.restart, lim.restart - stats.conflicts);

  reported = false;
  lim.report = 0;

  if (!incremental) {
    stable = opts.stabilize && opts.stabilizeonly;
    if (stable) LOG ("starting in always forced stable phase");
    else LOG ("starting in default non-stable phase");
    init_averages ();
  } else if (opts.stabilize && opts.stabilizeonly) {
    LOG ("keeping always forced stable phase");
    assert (stable);
  } else if (stable) {
    LOG ("switching back to default non-stable phase");
    stable = false;
    swap_averages ();
  } else LOG ("keeping non-stable phase");

  inc.stabilize = opts.stabilizeint;
  lim.stabilize = stats.conflicts + inc.stabilize;
  LOG ("new stabilize limit %ld after %ld conflicts",
    lim.stabilize, inc.stabilize);

  if (opts.stabilize && opts.reluctant) {
    LOG ("new restart reluctant doubling sequence period %d",
      opts.reluctant);
    reluctant.enable (opts.reluctant, opts.reluctantmax);
  } else reluctant.disable ();

  if (inc.conflicts < 0) {
    lim.conflicts = -1;
    LOG ("no limit on conflicts");
  } else {
    lim.conflicts = stats.conflicts + inc.conflicts;
    LOG ("conflict limit after %ld conflicts at %ld conflicts",
      inc.conflicts, lim.conflicts);
  }

  if (inc.decisions < 0) {
    lim.decisions = -1;
    LOG ("no limit on decisions");
  } else {
    lim.decisions = stats.decisions + inc.decisions;
    LOG ("conflict limit after %ld decisions at %ld decisions",
      inc.decisions, lim.decisions);
  }

  if (inc.preprocessing <= 0) {
    lim.preprocessing = 0;
    LOG ("no preprocessing");
  } else {
    lim.preprocessing = inc.preprocessing;
    LOG ("limiting to %d preprocessing rounds", lim.preprocessing);
  }

  if (inc.localsearch <= 0) {
    lim.localsearch = 0;
    LOG ("no local search");
  } else {
    lim.localsearch = inc.localsearch;
    LOG ("limiting to %d local search rounds", lim.localsearch);
  }

  lim.initialized = true;
}

/*------------------------------------------------------------------------*/

bool Internal::preprocess_round (int round) {
  (void) round;
  if (unsat) return false;
  if (!max_var) return false;
  START (preprocess);
  struct { int vars; long clauses; } before, after;
  before.vars = active ();
  before.clauses = stats.current.irredundant;
  stats.preprocessings++;
  assert (!preprocessing);
  preprocessing = true;
  PHASE ("preprocessing", stats.preprocessings,
    "starting round %d with %d variables and %ld clauses",
    round, before.vars, before.clauses);
  int old_elimbound = lim.elimbound;
  if (opts.probe) probe (false);
  if (opts.elim) elim (false);
  after.vars = active ();
  after.clauses = stats.current.irredundant;
  assert (preprocessing);
  preprocessing = false;
  PHASE ("preprocessing", stats.preprocessings,
    "finished round %d with %d variables and %ld clauses",
    round, after.vars, after.clauses);
  STOP (preprocess);
  report ('P');
  if (unsat) return false;
  if (after.vars < before.vars) return true;
  if (old_elimbound < lim.elimbound) return true;
  return false;
}

int Internal::preprocess () {
  if (opts.simplify)
    for (int i = 0; i < lim.preprocessing; i++)
      if (!preprocess_round (i))
        break;
  if (unsat) return 20;
  return 0;
}

/*------------------------------------------------------------------------*/

int Internal::try_to_satisfy_formula_by_saved_phases () {
  LOG ("satisfying formula by saved phases");
  assert (!level);
  assert (!force_saved_phase);
  assert (propagated == trail.size ());
  force_saved_phase = true;
  int res = 0;
  while (!res) {
    if (satisfied ()) {
      LOG ("formula indeed satisfied by saved phases");
      res = 10;
    } else if (decide ()) {
      LOG ("inconsistent assumptions with redundant clauses and phases");
      res = 20;
    } else if (!propagate ()) {
      LOG ("saved phases do not satisfy redundant clauses");
      assert (level > 0);
      backtrack ();
      conflict = 0;             // ignore conflict
      assert (!res);
      break;
    }
  }
  assert (force_saved_phase);
  force_saved_phase = false;
  return res;
}

/*------------------------------------------------------------------------*/

void Internal::produce_failed_assumptions () {
  LOG ("producing failed assumptions");
  assert (!level);
  assert (!assumptions.empty ());
  while (!unsat) {
    assert (!satisfied ());
    if (decide ()) break;
    while (!unsat && !propagate ())
      analyze ();
  }
  if (unsat) LOG ("formula is actually unsatisfiable unconditionally");
  else LOG ("assumptions indeed failing");
}

/*------------------------------------------------------------------------*/

int Internal::local_search_round (int round) {

  assert (round > 0);

  if (unsat) return false;
  if (!max_var) return false;

  START_OUTER_WALK ();
  assert (!localsearching);
  localsearching = true;

  // Determine propagation limit quadratically scaled with rounds.
  //
  long limit = opts.walkmineff;
  limit *= round;
  if (LONG_MAX / round > limit) limit *= round;
  else limit = LONG_MAX;

  int res = walk_round (limit, true);

  assert (localsearching);
  localsearching = false;
  STOP_OUTER_WALK ();

  report ('L');

  return res;
}

int Internal::local_search () {

  if (unsat) return 0;
  if (!max_var) return 0;
  if (!opts.walk) return 0;

  int res = 0;

  for (int i = 1; !res && i <= lim.localsearch; i++)
    res = local_search_round (i);

  if (res == 10) {
    LOG ("local search determined formula to be satisfiable");
    assert (!stats.walk.minimum);
    res = try_to_satisfy_formula_by_saved_phases ();
  } else if (res == 20) {
    LOG ("local search determined assumptions to be inconsistent");
    assert (!assumptions.empty ());
    produce_failed_assumptions ();
  }

  return res;
}

/*------------------------------------------------------------------------*/

int Internal::solve () {
  assert (clause.empty ());
  START (solve);
  if (level) backtrack ();
  int res = 0;
  if (unsat) {
    LOG ("already inconsistent");
    res = 20;
  } else if (!propagate ()) {
    LOG ("root level propagation produces conflict");
    learn_empty_clause ();
    res = 20;
  } else {

    init_limits ();

    if (!opts.restoreall &&
        external->tainted.empty ()) {
      LOG ("no tainted literals and nothing to restore");
      report ('*');
    } else {
      report ('+');
      external->restore_clauses ();
      internal->report ('r');
      if (!unsat && !propagate ()) {
        LOG ("root level propagation after restore produces conflict");
        learn_empty_clause ();
        res = 20;
      }
    }

    if (!res) res = preprocess ();
    if (!res) res = local_search ();
    if (!res) res = lucky_phases ();
    if (!res) {
      if (terminating ()) res = 0;
      else res = cdcl_loop_with_inprocessing ();
    }
  }
  if (termination_forced) {
    termination_forced = false;
    LOG ("reset forced termination");
  }
       if (res == 10) report ('1');
  else if (res == 20) report ('0');
  else                report ('?');
  STOP (solve);
  return res;
}

/*------------------------------------------------------------------------*/

void Internal::print_stats () {
  stats.print (this);
  if (checker) checker->print_stats ();
}

/*------------------------------------------------------------------------*/

// Only useful for debugging purposes.

void Internal::dump (Clause * c) {
  for (const auto & lit : *c)
    printf ("%d ", lit);
  printf ("0\n");
}

void Internal::dump () {
  long m = assumptions.size ();
  for (int idx = 1; idx <= max_var; idx++)
    if (fixed (idx)) m++;
  for (const auto & c : clauses)
    if (!c->garbage) m++;
  printf ("p cnf %d %ld\n", max_var, m);
  for (int idx = 1; idx <= max_var; idx++) {
    const int tmp = fixed (idx);
    if (tmp) printf ("%d 0\n", tmp < 0 ? -idx : idx);
  }
  for (const auto & c : clauses)
    if (!c->garbage) dump (c);
  for (const auto & lit : assumptions)
    printf ("%d 0\n", lit);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/

bool Internal::traverse_clauses (ClauseIterator & it) {
  vector<int> eclause;
  if (unsat) return it.clause (eclause);
  for (const auto & c : clauses) {
    if (c->garbage) continue;
    if (c->redundant) continue;
    bool satisfied = false;
    for (const auto & ilit : *c) {
      const int tmp = fixed (ilit);
      if (tmp > 0) { satisfied = true; break; }
      if (tmp < 0) continue;
      const int elit = externalize (ilit);
      eclause.push_back (elit);
    }
    if (!satisfied && !it.clause (eclause))
      return false;
    eclause.clear ();
  }
  return true;
}

}
