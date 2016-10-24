#include "clause.hpp"
#include "internal.hpp"
#include "iterator.hpp"
#include "macros.hpp"
#include "message.hpp"

#include <algorithm>

namespace CaDiCaL {

bool Internal::reducing () {
  if (!opts.reduce) return false;
  return stats.conflicts >= reduce_limit;
}

// Reason clauses (on non-zero decision level) can not be collected.
// We protect them before and unprotect them after garbage collection.

void Internal::protect_reasons () {
  for (const_int_iterator i = trail.begin (); i != trail.end (); i++) {
    Var & v = var (*i);
    if (!v.level || !v.reason) continue;
    v.reason->reason = true;
  }
}

void Internal::unprotect_reasons () {
  for (const_int_iterator i = trail.begin (); i != trail.end (); i++) {
    Var & v = var (*i);
    if (!v.level || !v.reason) continue;
    assert (v.reason->reason), v.reason->reason = false;
  }
}

// Clause with smaller glucose level (glue) are considered more useful.
// Then we use the 'resolved' time stamp as a tie breaker.  So more recently
// resolved clauses are preferred to keep (if they have the same glue).

struct less_usefull {
  bool operator () (Clause * c, Clause * d) {
    if (c->glue > d->glue) return true;
    if (c->glue < d->glue) return false;
    return resolved_earlier () (c, d);
  }
};

// This function implements the important reduction policy. It determines
// which redundant clauses are considered not useful and thus will be
// collected in a subsequent garbage collection phase.

void Internal::mark_useless_redundant_clauses_as_garbage () {
  vector<Clause*> stack;
  stack.reserve (stats.redundant);
  for (const_clause_iterator i = clauses.begin (); i != clauses.end (); i++) {
    Clause * c = *i;
    if (!c->redundant) continue;            // keep irredundant
    if (c->reason) continue;                // need to keep reasons
    if (c->garbage) continue;               // already marked
    if (c->size <= opts.keepsize) continue; // keep small size clauses
    if (c->glue <= opts.keepglue) continue; // keep small glue clauses
    if (c->resolved () > recently_resolved) continue;
    stack.push_back (c);
  }
  if (opts.reduceglue)
    stable_sort (stack.begin (), stack.end (), resolved_earlier ());
  else
    stable_sort (stack.begin (), stack.end (), less_usefull ());

  const_clause_iterator target = stack.begin () + stack.size ()/2;
  for (const_clause_iterator i = stack.begin (); i != target; i++) {
    LOG (*i, "marking useless to be collected");
    (*i)->garbage = true;
  }
}

/*------------------------------------------------------------------------*/

void Internal::reduce () {
  START (reduce);
  stats.reductions++;
  report ('R', 1);
  protect_reasons ();
  mark_satisfied_clauses_as_garbage ();
  mark_useless_redundant_clauses_as_garbage ();
  garbage_collection ();
  unprotect_reasons ();
  reduce_inc += reduce_inc_inc;
  if (reduce_inc_inc > 1) reduce_inc_inc--;
  reduce_limit = stats.conflicts + reduce_inc;
  recently_resolved = stats.resolved;
  report ('-');
  STOP (reduce);
}

};
