#include "clause.hpp"
#include "internal.hpp"
#include "iterator.hpp"
#include "macros.hpp"
#include "message.hpp"
#include "proof.hpp"

#include <algorithm>

namespace CaDiCaL {

// Code for conflict analysis, e.g., to generate the first UIP clause.  The
// main function is 'analyze' below.  It further uses 'minimize' to minimize
// the first UIP clause, which is in 'minimize.cpp'.  An important side
// effect of conflict analysis is to update the decision queue by bumping
// variables.  Similarly resolved clauses are bumped to mark them as active.

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

void Internal::bump_variable (int lit) {
  const int idx = vidx (lit);
  Link * l = ltab + idx;
  if (!l->next) return;
  queue.dequeue (ltab, l);
  queue.enqueue (ltab, l);
  btab[idx] = ++stats.bumped;
  LOG ("moved to front %d and bumped %ld", idx, btab[idx]);
  if (!vals[idx]) update_queue_unassigned (idx);
}

// Initially we proposed to bump the variable in the current 'bumped' stamp
// order only.  This maintains the current order between bumped variables.
// On few benchmarks this however lead to a large number of propagations per
// seconds, which can be reduced by an order of magnitude by focusing
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
    long s = internal->bumped (a) + internal->var (a).trail;
    long t = internal->bumped (b) + internal->var (b).trail;
    return s < t;
  }
};

void Internal::bump_variables () {
  START (bump);
  reverse (analyzed.begin (), analyzed.end ());
  stable_sort (analyzed.begin (), analyzed.end (), bump_earlier (this));
  for (const_int_iterator i = analyzed.begin (); i != analyzed.end (); i++)
    bump_variable (*i);
  STOP (bump);
}

/*------------------------------------------------------------------------*/

// Clause activity is replaced by a move-to-front scheme as well with
// 'resolved' as time stamp.  Only long and high glue clauses are stamped
// since small or low glue clauses are kept anyhow (and do not actually have
// a 'resolved' field).  We keep the relative order of bumped clauses by
// sorting them first.

void Internal::bump_resolved_clauses () {
  if (!opts.resolve) { assert (resolved.empty ()); return; }
  START (bump);
  sort (resolved.begin (), resolved.end (), resolved_earlier ());
  for (const_clause_iterator i = resolved.begin (); i != resolved.end (); i++)
    (*i)->resolved () = ++stats.resolved;
  STOP (bump);
  resolved.clear ();
}

inline void Internal::resolve_clause (Clause * c) {
  if (!c->redundant) return;
  if (c->size <= opts.keepsize) return;
  if (c->glue <= opts.keepglue) return;
  assert (c->extended);
  resolved.push_back (c);
}

/*------------------------------------------------------------------------*/

// During conflict analysis literals not seen yet either become part of the
// first UIP clause (if on lower decision level), are dropped (if fixed),
// or are resolved away (if on the current decision level and different from
// the first UIP).  At the same time we update the number of seen literals on
// a decision level and the smallest trail position of a seen literal for
// each decision level.  This both helps conflict clause minimization.  The
// number of seen levels is the glucose level (also called glue, or LBD).

inline void Internal::analyze_literal (int lit, int & open) {
  assert (lit);
  Flags & f = flags (lit);
  if (f.seen ()) return;
  Var & v = var (lit);
  if (!v.level) return;
  assert (val (lit) < 0);
  if (v.level < level) clause.push_back (lit);
  Level & l = control[v.level];
  if (!l.seen++) {
    LOG ("found new level %d contributing to conflict", v.level);
    levels.push_back (v.level);
  }
  if (v.trail < l.trail) l.trail = v.trail;
  f.set (SEEN);
  analyzed.push_back (lit);
  LOG ("analyzed literal %d assigned at level %d", lit, v.level);
  if (v.level == level) open++;
}


inline void
Internal::analyze_reason (int lit, Clause * reason, int & open) {
  assert (reason);
  if (opts.resolve) resolve_clause (reason);
  const const_literal_iterator end = reason->end ();
  const_literal_iterator j = reason->begin ();
  int other;
  while (j != end)
    if ((other = *j++) != lit)
      analyze_literal (other, open);
}

/*------------------------------------------------------------------------*/

void Internal::clear_seen () {
  for (const_int_iterator i = analyzed.begin (); i != analyzed.end (); i++)
    flags (*i).reset ();
  analyzed.clear ();
}

void Internal::clear_levels () {
  for (const_int_iterator i = levels.begin (); i != levels.end (); i++)
    control[*i].reset ();
  levels.clear ();
}

/*------------------------------------------------------------------------*/

// By sorting the first UIP clause literals, we establish the invariant that
// the two watched literals are on the largest decision highest level.

struct trail_greater {
  Internal * internal;
  trail_greater (Internal * s) : internal (s) { }
  bool operator () (int a, int b) {
    return internal->var (a).trail > internal->var (b).trail;
  }
};

void Internal::analyze () {
  assert (conflict);
  if (!level) { learn_empty_clause (); conflict = 0; return; }

  START (analyze);

  // First derive the first UIP clause.
  //
  Clause * reason = conflict;
  LOG (reason, "analyzing conflict");
  int open = 0, uip = 0, other = 0;
  const_int_iterator i = trail.end ();
  for (;;) {
    if (reason) analyze_reason (uip, reason, open);
    else analyze_literal (other, open);
    while (!seen (uip = *--i))
      ;
    if (!--open) break;
    Var & v = var (uip);
    if (!(reason = v.reason)) other = v.other;
#ifdef LOGGING
    if (reason) LOG (reason, "analyzing %d reason", uip);
    else LOG ("analyzing %d binary reason %d %d", uip, uip, other);
#endif
  }
  LOG ("first UIP %d", uip);
  clause.push_back (-uip);
  check_clause ();

  // Update glue statistics.
  //
  bump_resolved_clauses ();
  const int glue = (int) levels.size ();
  LOG ("1st UIP clause of size %d and glue %d", (int) clause.size (), glue);
  UPDATE_AVG (fast_glue_avg, glue);
  UPDATE_AVG (slow_glue_avg, glue);

  if (opts.minimize) minimize_clause ();     // minimize clause

  stats.units += (clause.size () == 1);
  stats.binaries += (clause.size () == 2);

  if (opts.sublast) eagerly_subsume_last_learned ();

  // Determine back jump level, backtrack and assign flipped literal.
  //
  Clause * driving_clause = 0;
  int jump = 0;
  if (clause.size () > 1) {
    stable_sort (clause.begin (), clause.end (), trail_greater (this));
    driving_clause = new_learned_clause (glue);
    jump = var (clause[1]).level;
  }
  UPDATE_AVG (jump_avg, jump);
  backtrack (jump);
  assign (-uip, driving_clause);

  bump_variables ();                         // Update decision heuristics.

  // Clean up.
  //
  clear_seen ();
  clause.clear ();
  clear_levels ();
  conflict = 0;

  STOP (analyze);
}

// We wait reporting a learned unit until propagation of that unit is
// completed.  Otherwise the 'i' report line might prematurely give the
// number of remaining variables.

void Internal::iterate () { iterating = false; report ('i'); }

};
