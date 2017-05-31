#include "internal.hpp"

namespace CaDiCaL {

// Once in a while reduce, e.g., remove, learned clauses which are supposed
// to be less useful in the future.  This is done in increasing intervals,
// which has the effect of allowing more and more learned clause to be kept
// for a longer period.

bool Internal::reducing () {
  return stats.conflicts >= lim.reduce;
}

/*------------------------------------------------------------------------*/

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

/*------------------------------------------------------------------------*/

// Clauses with smaller glucose level (also called 'glue' or 'LBD') are
// considered more useful following the observations made by the Glucose
// team in their IJCAI'09 paper.  Then we use the 'analyzed' time stamp as a
// tie breaker.  Thus more recently resolved clauses are preferred to be
// kept if they have the same glue.

struct less_usefull {
  Internal * internal;
  less_usefull (Internal * i) : internal (i) { }
  bool operator () (Clause * c, Clause * d) {
    double p = internal->clause_useful (c);
    double q = internal->clause_useful (d);
    return p < q;
  }
};

void Internal::update_clause_useful_probability (Clause * c, bool used) {
  assert (!c->keep);
  double predicted = clause_useful (c);
  double actual = used ? 1 : 0;
  double error = actual - predicted;
  LOG ("glue %d, size %u, predicted %1.4f, actual %.0f, error %.0f%%",
    c->glue, c->size, predicted, actual, percent (error, predicted));
  LOG ("old prediction %1.4f = %f / %d + %f / %u",
    predicted, wg, c->glue, ws, c->size);
  wg += (error / c->glue) * 1e-5;
  ws += (error / c->size) * 1e-5;
  LOG ("new prediction %1.4f = %f / %d + %f / %u",
    predicted, wg, c->glue, ws, c->size);
  LOG ("actual prediction %1.4f = %f / %d + %f / %u",
    clause_useful (c), wg, c->glue, ws, c->size);
}

// This function implements the important reduction policy. It determines
// which redundant clauses are considered not useful and thus will be
// collected in a subsequent garbage collection phase.

void Internal::mark_useless_redundant_clauses_as_garbage () {
  vector<Clause*> stack;
  stack.reserve (stats.redundant);
  const_clause_iterator end = clauses.end (), i;
  for (i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (!c->redundant) continue;                // keep irredundant
    if (c->garbage) continue;                   // already marked
    if (c->reason) continue;                    // need to keep reasons
    const bool used = c->used;
    c->used = false;
    if (c->hbr) {                               // hyper binary resolvent?
      assert (c->size == 2);
      if (!used) mark_garbage (c);		// keep it for one round
      continue;
    }
    if (c->keep) continue;             		// statically considered useful
    update_clause_useful_probability (c, used);
    if (used) continue;				// keep recently used
    stack.push_back (c);
  }

  VRB ("reduce", stats.reductions,
    "useful:  %f / glue + %f / size",
    stats.reductions, wg, ws);

  stable_sort (stack.begin (), stack.end (), less_usefull (this));

  const_clause_iterator target = stack.begin () + stack.size ()/2;
  for (const_clause_iterator i = stack.begin (); i != target; i++) {
    LOG (*i, "marking useless to be collected");
    mark_garbage (*i);
    stats.reduced++;
  }

  lim.keptsize = lim.keptglue = 0;
  end = stack.end ();
  for (i = target; i != end; i++) {
    Clause * c = *i;
    if (c->size > lim.keptsize) lim.keptsize = c->size;
    if (c->glue > lim.keptglue) lim.keptglue = c->glue;
  }

  VRB ("reduce", stats.reductions,
    "maximum kept size %d glue %d", lim.keptsize, lim.keptglue);
}

/*------------------------------------------------------------------------*/

void Internal::reduce () {
  START (reduce);
  stats.reductions++;
  report ('+', 1);
  protect_reasons ();
  mark_satisfied_clauses_as_garbage ();
  mark_useless_redundant_clauses_as_garbage ();
  garbage_collection ();
  unprotect_reasons ();
  inc.reduce += inc.redinc;
  if (inc.redinc > 1) inc.redinc--;
  lim.reduce = stats.conflicts + inc.reduce;
  lim.conflicts_at_last_reduce = stats.conflicts;
  report ('-');
  STOP (reduce);
}

};
