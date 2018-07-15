#include "internal.hpp"

namespace CaDiCaL {

// Once in a while reduce, e.g., remove, learned clauses which are supposed
// to be less useful in the future.  This is done in increasing intervals,
// which has the effect of allowing more and more learned clause to be kept
// for a longer period.

bool Internal::reducing () {
  if (!opts.learn) return false;
  if (!opts.reduce) return false;
  if (stats.conflicts < lim.conflicts_at_last_restart +
        opts.reducewait * relative (stats.conflicts, stats.restarts))
    return false;
  return stats.conflicts >= lim.reduce;
}

/*------------------------------------------------------------------------*/

// Even less regularly we are flushing all redundant clauses.

bool Internal::flushing () {
  if (!opts.flush) return false;
  return stats.conflicts >= lim.flush;
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

void Internal::mark_clauses_to_be_flushed () {
  const_clause_iterator end = clauses.end (), i;
  for (i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (!c->redundant) continue; // keep irredundant
    if (c->garbage) continue;    // already marked as garbage
    if (c->reason) continue;     // need to keep reasons
    const bool used = c->used;
    c->used = false;
    if (used) continue;
    mark_garbage (c);            // flush unused clauses
    stats.flushed++;
  }
  // no change to 'lim.kept{size,glue}'
}

/*------------------------------------------------------------------------*/

// Clauses of larger glue or size are considered less useful.  We partially
// follow the observations made by the Glucose team in their IJCAI'09 paper
// and keep all low glucose level clauses limited by 'options.keepglue'
// (typically '3').  Recently unused candidate clauses to be collected
// are sorted by size, which is a mix of glue, then activity, and then size
// order.  Note, that during 'stabilization' phases with no restarts, we
// keep 'options.stableglue' clauses, which by default is higher than
// 'options.keepglue' (typically '5').  However, if the 'option.reduceglue'
// is set we also compare glue, i.e., always if it is larger than one or
// just during stabilization phases if it is only one.

struct less_useful {
  const bool compare_glue;
  less_useful (Internal * i) :
    compare_glue ( i->opts.reduceglue > 1 ||
                  (i->opts.reduceglue > 0 && i->stabilization)) { }
  bool operator () (Clause * c, Clause * d) {
    if (compare_glue && c->glue > d->glue) return true;
    if (compare_glue && c->glue < d->glue) return false;
    return c->size > d->size;
  }
};

// This function implements the important reduction policy. It determines
// which redundant clauses are considered not useful and thus will be
// collected in a subsequent garbage collection phase.

void Internal::mark_useless_redundant_clauses_as_garbage () {

  vector<Clause*> stack;
  stack.reserve (stats.redundant);
  const_clause_iterator end = clauses.end (), i;

  for (i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (!c->redundant) continue;    // keep irredundant
    if (c->garbage) continue;       // skip already marked
    if (c->reason) continue;        // need to keep reasons
    const bool used = c->used;
    c->used = false;
    if (c->hbr) {                   // Hyper binary resolvents are only
      assert (c->size == 2);        // kept for one round (even though
      if (!used) mark_garbage (c);  // 'c->keep' is true) unless they
      continue;                     // were recently used.
    }
    if (used) continue;		    // keep recently used
    if (c->keep) continue;          // forced to keep (see above)
    if (stabilization && c->stable) // keep during stabilization
      continue;
    stack.push_back (c);
  }

  stable_sort (stack.begin (), stack.end (), less_useful (this));

  const_clause_iterator target = stack.begin () + stack.size ()/2;
  for (const_clause_iterator i = stack.begin (); i != target; i++) {
    LOG (*i, "marking useless to be collected");
    mark_garbage (*i);
    stats.reduced++;
  }

  lim.keptsize = lim.keptglue = 0;
  end = stack.end ();
  for (i = target; i != end; i++) {
    const Clause * c = *i;
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

  bool flush = flushing ();
  if (flush) stats.flushings++;

  if (level) protect_reasons ();
  mark_satisfied_clauses_as_garbage ();
  if (flush) mark_clauses_to_be_flushed ();
  else mark_useless_redundant_clauses_as_garbage ();
  garbage_collection ();
  if (level) unprotect_reasons ();

  assert (opts.learn);
  inc.reduce += inc.redinc;
  if (inc.reduce > opts.reducemax) inc.reduce = opts.reducemax;
  else if (inc.redinc > 1l) inc.redinc--;
  assert (inc.reduce > 0l);
  VRB ("reduce", stats.reductions,
    "new reduce increment %ld", inc.reduce);
  lim.reduce = stats.conflicts + inc.reduce;
  VRB ("reduce", stats.reductions,
    "new reduce limit %ld", lim.reduce);
  lim.conflicts_at_last_reduce = stats.conflicts;

  if (flush) {
    VRB ("flush", stats.flushed, "new flush increment %ld", inc.flush);
    inc.flush *= opts.flushfactor;
    lim.flush = stats.conflicts + inc.flush;
    VRB ("flush", stats.flushed, "new flush limit %ld", lim.flush);
  }

  report (flush ? 'f' : '-');
  STOP (reduce);
}

};
