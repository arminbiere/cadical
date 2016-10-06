#include "cadical.hpp"

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
  if (var (queue.assigned).bumped >= v->bumped) return;
  queue.assigned = idx;
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

};
