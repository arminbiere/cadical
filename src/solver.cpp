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

void Solver::learn_empty_clause () {
  assert (!unsat);
  LOG ("learned empty clause");
  if (proof) proof->trace_empty_clause ();
  unsat = true;
}

void Solver::learn_unit_clause (int lit) {
  LOG ("learned unit clause %d", lit);
  if (proof) proof->trace_unit_clause (lit);
  iterating = true;
  stats.fixed++;
}

/*------------------------------------------------------------------------*/

void Solver::assign (int lit, Clause * reason) {
  int idx = vidx (lit);
  assert (!vals[idx]);
  Var & v = vars[idx];
  if (!(v.level = level)) learn_unit_clause (lit);
  v.reason = reason;
  vals[idx] = phases[idx] = sign (lit);
  assert (val (lit) > 0);
  v.trail = (int) trail.size ();
  trail.push_back (lit);
  LOG (reason, "assign %d", lit);
}

void Solver::unassign (int lit) {
  assert (val (lit) > 0);
  int idx = vidx (lit);
  vals[idx] = 0;
  LOG ("unassign %d", lit);
  Var * v = vars + idx;
  if (queue.assigned->bumped >= v->bumped) return;
  queue.assigned = v;
  LOG ("queue next moved to %d", idx);
}

void Solver::backtrack (int target_level) {
  assert (target_level <= level);
  if (target_level == level) return;
  LOG ("backtracking to decision level %d", target_level);
  int decision = levels[target_level + 1].decision, lit;
  do {
    unassign (lit = trail.back ());
    trail.pop_back ();
  } while (lit != decision);
  if (trail.size () < next.watches) next.watches = trail.size ();
  if (trail.size () < next.binaries) next.binaries = trail.size ();
  levels.resize (target_level + 1);
  level = target_level;
}

/*------------------------------------------------------------------------*/

bool Solver::minimize_literal (int lit, int depth) {
  Var & v = var (lit);
  if (!v.level || v.removable || (depth && v.seen)) return true;
  if (!v.reason || v.poison || v.level == level) return false;
  const Level & l = levels[v.level];
  if ((!depth && l.seen < 2) || v.trail <= l.trail) return false;
  if (depth > opts.minimizedepth) return false;
  const int size = v.reason->size, * lits = v.reason->literals;
  bool res = true;
  for (int i = 0, other; res && i < size; i++)
    if ((other = lits[i]) != lit)
      res = minimize_literal (-other, depth+1);
  if (res) v.removable = true; else v.poison = true;
  seen.minimized.push_back (lit);
  if (!depth) LOG ("minimizing %d %s", lit, res ? "succeeded" : "failed");
  return res;
}

struct trail_smaller_than {
  Solver * solver;
  trail_smaller_than (Solver * s) : solver (s) { }
  bool operator () (int a, int b) {
    return solver->var (a).trail < solver->var (b).trail;
  }
};

void Solver::minimize_clause () {
  if (!opts.minimize) return;
  START (minimize);
  sort (clause.begin (), clause.end (), trail_smaller_than (this));
  LOG (clause, "minimizing first UIP clause");
  assert (seen.minimized.empty ());
  stats.literals.learned += clause.size ();
  size_t j = 0;
  for (size_t i = 0; i < clause.size (); i++)
    if (minimize_literal (-clause[i])) stats.literals.minimized++;
    else clause[j++] = clause[i];
  LOG ("minimized %d literals", clause.size () - j);
  clause.resize (j);
  for (size_t i = 0; i < seen.minimized.size (); i++) {
    Var & v = var (seen.minimized[i]);
    v.removable = v.poison = false;
  }
  seen.minimized.clear ();
  STOP (minimize);
#ifndef NDEBUG
  check_clause ();
#endif
}

};
