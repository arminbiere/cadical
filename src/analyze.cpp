#include "internal.hpp"

#include <algorithm>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

void Internal::learn_empty_clause () {
  assert (!unsat);
  LOG ("learned empty clause");
  if (proof) proof->trace_empty_clause ();
  unsat = true;
}

void Internal::learn_unit_clause (int lit) {
  LOG ("learned unit clause %d", lit);
  if (proof) proof->trace_unit_clause (lit);
  iterating = true;
  stats.fixed++;
}

/*------------------------------------------------------------------------*/

// Important variables recently used in conflict analysis are 'bumped',
// which means to move them to the front of the VMTF decision queue.  The
// 'bumped' time stamp is updated accordingly.  It is used to determine
// whether the 'queue.assigned' pointer has to be moved in 'unassign'.

void Internal::bump_variable (Var * v) {
  if (!v->next) return;
  if (queue.assigned == v) queue.assigned = v->prev ? v->prev : v->next;
  queue.dequeue (v), queue.enqueue (v);
  v->bumped = ++stats.bumped;
  int idx = var2idx (v);
  if (!vals[idx]) queue.assigned = v;
  LOG ("VMTF bumped and moved to front %d", idx);
}

// Initially we proposed to bump the variable in the current 'bumped' stamp
// order.  This maintains the current order between bumped variables.  On
// few benchmarks this however lead to a large number of propagations per
// seconds, which can be reduce by an order of magnitude by focusing
// somewhat on recently assigned variables more, particularly in this
// situation.  This can easily be achieved by using the sum of the 'bumped'
// time stamp and trail height 'trail' for comparison.  Note that 'bumped'
// is always increasing and gets really large, while 'trail' can never be
// larger than the number of variables, so there is likely a potential for
// further optimization.

struct bump_earlier {
  Internal * internal;
  bump_earlier (Internal * s) : internal (s) { }
  bool operator () (int a, int b) {
    Var & u = internal->var (a), & v = internal->var (b);
    return u.bumped + u.trail < v.bumped + v.trail;
  }
};

void Internal::bump_and_clear_seen_variables () {
  START (bump);
  sort (seen.begin (), seen.end (), bump_earlier (this));
  for (const_int_iterator i = seen.begin (); i != seen.end (); i++) {
    Var * v = &var (*i);
    assert (v->seen);
    v->seen = false;
    bump_variable (v);
  }
  seen.clear ();
  STOP (bump);
}

/*------------------------------------------------------------------------*/

// Clause activity is replaced by a move to front scheme as well with
// 'resolved' as time stamp.  Only long and high glue clauses are stamped
// since small or low glue clauses are kept anyhow (and do not actually have
// a 'resolved' field).  We keep the relative order of bumped clauses by
// sorting them first.

void Internal::bump_resolved_clauses () {
  START (bump);
  sort (resolved.begin (), resolved.end (), resolved_earlier ());
  for (const_clause_iterator i = resolved.begin (); i != resolved.end (); i++)
    (*i)->resolved () = ++stats.resolved;
  STOP (bump);
  resolved.clear ();
}

void Internal::resolve_clause (Clause * c) {
  if (!c->redundant) return;
  if (c->size <= opts.keepsize) return;
  if (c->glue <= opts.keepglue) return;
  assert (c->extended);
  resolved.push_back (c);
}

/*------------------------------------------------------------------------*/

// During conflict analysis literals not seen yet either become part of the
// first-uip clauses (if on lower decision level), are dropped (if fixed),
// or are resolved away (if on the current decision level and different from
// the first UIP).  At the same time we update the number of seen literals on
// a decision level and the smallest trail position of a seen literal for
// each decision level.  This both helps conflict clause minimization.  The
// number of seen levels is the glucose level (also called glue, or LBD).

bool Internal::analyze_literal (int lit) {
  Var & v = var (lit);
  if (v.seen) return false;
  if (!v.level) return false;
  assert (val (lit) < 0);
  if (v.level < level) clause.push_back (lit);
  Level & l = control[v.level];
  if (!l.seen++) {
    LOG ("found new level %d contributing to conflict", v.level);
    levels.push_back (v.level);
  }
  if (v.trail < l.trail) l.trail = v.trail;
  v.seen = true;
  seen.push_back (lit);
  LOG ("analyzed literal %d assigned at level %d", lit, v.level);
  return v.level == level;
}

void Internal::clear_levels () {
  for (const_int_iterator i = levels.begin (); i != levels.end (); i++)
    control[*i].reset ();
  levels.clear ();
}

// By sorting the first UIP clause literals before minimization, we
// establish the invariant that the two watched literals are on the largest
// decision highest level.

struct trail_greater_than {
  Internal * internal;
  trail_greater_than (Internal * s) : internal (s) { }
  bool operator () (int a, int b) {
    return internal->var (a).trail > internal->var (b).trail;
  }
};

void Internal::analyze () {
  assert (conflict);
  if (!level) { learn_empty_clause (); conflict = 0; return; }
  START (analyze);
  assert (clause.empty ());
  assert (seen.empty ());
  assert (levels.empty ());
  assert (minimized.empty ());
  assert (resolved.empty ());
  Clause * reason = conflict;
  LOG (reason, "analyzing conflict");
  resolve_clause (reason);
  int open = 0, uip = 0;
  const_int_iterator i = trail.end ();
  for (;;) {
    const int size = reason->size, * lits = reason->literals;;
    for (int j = 0; j < size; j++)
      if (analyze_literal (lits[j])) open++;
    while (!var (uip = *--i).seen)
      ;
    if (!--open) break;
    reason = var (uip).reason;
    LOG (reason, "analyzing %d reason", uip);
  }
  LOG ("first UIP %d", uip);
  clause.push_back (-uip);
  check_clause ();
  bump_resolved_clauses ();
  const int size = (int) clause.size ();
  const int glue = (int) levels.size ();
  LOG ("1st UIP clause of size %d and glue %d", size, glue);
  UPDATE_AVG (fast_glue_avg, glue);
  UPDATE_AVG (slow_glue_avg, glue);
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
  UPDATE_AVG (jump_avg, jump);
  backtrack (jump);
  assign (-uip, driving_clause);
  bump_and_clear_seen_variables ();
  clause.clear (), clear_levels ();
  conflict = 0;
  STOP (analyze);
}

// We wait reporting a learned unit until propagation of that unit is
// completed.  Otherwise the 'i' report line might prematurely give the
// number of remaining variables.

void Internal::iterate () { iterating = false; report ('i'); }

};
