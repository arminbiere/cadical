#include "solver.hpp"

#include <algorithm>

namespace CaDiCaL {

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

