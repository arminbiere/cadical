#include "solver.hpp"

#include <algorithm>

namespace CaDiCaL {

void Solver::bump_variable (Var * v, int uip) {
  if (!v->next) return;
  if (queue.assigned == v)
    queue.assigned = v->prev ? v->prev : v->next;
  queue.dequeue (v), queue.enqueue (v);
  v->bumped = ++stats.bumped;
  int idx = v - vars;
  if (idx != uip && !vals[idx]) queue.assigned = v;
  LOG ("VMTF bumped and moved to front %d", idx);
}

struct bump_earlier {
  Solver * solver;
  bump_earlier (Solver * s) : solver (s) { }
  bool operator () (int a, int b) {
    Var & u = solver->var (a), & v = solver->var (b);
    return u.bumped + u.trail < v.bumped + v.trail;
  }
};

void Solver::bump_and_clear_seen_variables (int uip) {
  START (bump);
  sort (seen.literals.begin (), seen.literals.end (), bump_earlier (this));
  if (uip < 0) uip = -uip;
  for (size_t i = 0; i < seen.literals.size (); i++) {
    int idx = vidx (seen.literals[i]);
    Var * v = vars + idx;
    assert (v->seen);
    v->seen = false;
    bump_variable (v, uip);
  }
  seen.literals.clear ();
  STOP (bump);
}

void Solver::bump_resolved_clauses () {
  START (bump);
  sort (resolved.begin (), resolved.end (), resolved_earlier ());
  for (size_t i = 0; i < resolved.size (); i++)
    resolved[i]->resolved = ++stats.resolved;
  STOP (bump);
  resolved.clear ();
}

void Solver::resolve_clause (Clause * c) {
  if (!c->redundant) return;
  if (c->size <= opts.keepsize) return;
  if (c->glue <= opts.keepglue) return;
  resolved.push_back (c);
}

bool Solver::analyze_literal (int lit) {
  Var & v = var (lit);
  if (v.seen) return false;
  if (!v.level) return false;
  assert (val (lit) < 0);
  if (v.level < level) clause.push_back (lit);
  Level & l = levels[v.level];
  if (!l.seen++) {
    LOG ("found new level %d contributing to conflict");
    seen.levels.push_back (v.level);
  }
  if (v.trail < l.trail) l.trail = v.trail;
  v.seen = true;
  seen.literals.push_back (lit);
  LOG ("analyzed literal %d assigned at level %d", lit, v.level);
  return v.level == level;
}

void Solver::clear_levels () {
  for (size_t i = 0; i < seen.levels.size (); i++)
    levels[seen.levels[i]].reset ();
  seen.levels.clear ();
}

struct trail_greater_than {
  Solver * solver;
  trail_greater_than (Solver * s) : solver (s) { }
  bool operator () (int a, int b) {
    return solver->var (a).trail > solver->var (b).trail;
  }
};

void Solver::analyze () {
  assert (conflict);
  assert (clause.empty ());
  assert (seen.literals.empty ());
  assert (seen.levels.empty ());
  assert (seen.minimized.empty ());
  assert (resolved.empty ());
  START (analyze);
  if (!level) learn_empty_clause ();
  else {
    Clause * reason = conflict;
    LOG (reason, "analyzing conflict");
    resolve_clause (reason);
    int open = 0, uip = 0;
    size_t i = trail.size ();
    for (;;) {
      const int size = reason->size, * lits = reason->literals;;
      for (int j = 0; j < size; j++)
        if (analyze_literal (lits[j])) open++;
      while (!var (uip = trail[--i]).seen)
        ;
      if (!--open) break;
      reason = var (uip).reason;
      LOG (reason, "analyzing %d reason", uip);
    }
    LOG ("first UIP %d", uip);
    clause.push_back (-uip);
#ifndef NDEBUG
    check_clause ();
#endif
    bump_resolved_clauses ();
    const int size = (int) clause.size ();
    const int glue = (int) seen.levels.size ();
    LOG ("1st UIP clause of size %d and glue %d", size, glue);
    UPDATE (glue.slow, glue);
    UPDATE (glue.fast, glue);
    if (blocking.enabled) UPDATE (glue.blocking, glue);
    else                  UPDATE (glue.nonblocking, glue);
    if (opts.minimize) minimize_clause ();
    Clause * driving_clause = 0;
    int jump = 0;
    if (size > 1) {
      sort (clause.begin (), clause.end (), trail_greater_than (this));
      driving_clause = new_learned_clause (glue);
      jump = var (clause[1]).level;
    }
    stats.learned.unit += (size == 1);
    stats.learned.binary += (size == 2);
    UPDATE (frequency.unit, (size == 1) ? inc.unit : 0);
    UPDATE (jump, jump);
    UPDATE (trail, trail.size ());
    if (opts.restartblocking &&
        stats.conflicts >= limits.restart.conflicts &&
        blocking_enabled () &&
        trail.size () > opts.restartblock * avg.trail) {
      LOG ("blocked restart");
      limits.restart.conflicts = stats.conflicts + opts.restartint;
      stats.restart.blocked++;
    }
    backtrack (jump);
    assign (-uip, driving_clause);
    bump_and_clear_seen_variables (uip);
    clause.clear (), clear_levels ();
  }
  conflict = 0;
  STOP (analyze);
}

};
