#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Once in a while we reduce, e.g., we remove learned clauses which are
// supposed to be less useful in the future.  This is done in increasing
// intervals, which has the effect of allowing more and more learned clause
// to be kept for a longer period.  The number of learned clauses kept
// in memory corresponds to an upper bound on the 'space' of a resolution
// proof needed to refute a formula in proof complexity sense.

bool Internal::reducing () {
  if (!opts.reduce) return false;
  if (!stats.current.redundant) return false;
  return stats.conflicts >= lim.reduce;
}

/*------------------------------------------------------------------------*/

// Even less regularly we are flushing all redundant clauses.

bool Internal::flushing () {
  if (!opts.flush) return false;
  return stats.conflicts >= lim.flush;
}

/*------------------------------------------------------------------------*/

void Internal::mark_clauses_to_be_flushed () {
  for (const auto & c : clauses) {
    if (!c->redundant) continue; // keep irredundant
    if (c->garbage) continue;    // already marked as garbage
    if (c->reason) continue;     // need to keep reasons
    const unsigned used = c->used;
    if (used) c->used--;
    if (used) continue;          // but keep recently used clauses
    mark_garbage (c);            // flush unused clauses
    if (c->hyper) stats.flush.hyper++;
    else stats.flush.learned++;
  }
  // No change to 'lim.kept{size,glue}'.
}

/*------------------------------------------------------------------------*/

// Clauses of larger glue or larger size are considered less useful.
//
// We also follow the observations made by the Glucose team in their
// IJCAI'09 paper and keep all low glue clauses limited by
// 'options.keepglue' (typically '2').
//
// In earlier versions we pre-computed a 64-bit sort key per clause and
// wrapped a pointer to the clause and the 64-bit sort key into a separate
// data structure for sorting.  This was probably faster but awkward and
// so we moved back to a simpler scheme which also uses 'stable_sort'
// instead of 'rsort' below.  Sorting here is not a hot-spot anyhow.

struct reduce_less_useful {
  bool operator () (const Clause * c, const Clause * d) const {
    if (c->glue > d->glue) return true;
    if (c->glue < d->glue) return false;
    return c->size > d->size;
  }
};

// This function implements the important reduction policy. It determines
// which redundant clauses are considered not useful and thus will be
// collected in a subsequent garbage collection phase.

void Internal::mark_useless_redundant_clauses_as_garbage () {

  // We use a separate stack for sorting candidates for removal.  This uses
  // (slightly) more memory but has the advantage to keep the relative order
  // in 'clauses' intact, which actually due to using stable sorting goes
  // into the candidate selection (more recently learned clauses are kept if
  // they otherwise have the same glue and size).

  vector<Clause *> stack;

  stack.reserve (stats.current.redundant);

  for (const auto & c : clauses) {
    if (!c->redundant) continue;    // Keep irredundant.
    if (c->garbage) continue;       // Skip already marked.
    if (c->reason) continue;        // Need to keep reasons.
    const unsigned used = c->used;
    if (used) c->used--;
    if (c->hyper) {                 // Hyper binary and ternary resolvents
      assert (c->size <= 3);        // are only kept for one reduce round
      if (!used) mark_garbage (c);  // (even if 'c->keep' is true) unless
      continue;                     //  used recently.
    }
    if (used) continue;             // Do keep recently used clauses.
    if (c->keep) continue;          // Forced to keep (see above).

    stack.push_back (c);
  }

  stable_sort (stack.begin (), stack.end (), reduce_less_useful ());

  size_t target = 1e-2 * opts.reducetarget * stack.size ();

  // This is defensive code, which I usually consider a bug, but here I am
  // just not sure that using floating points in the line above is precise
  // in all situations and instead of figuring that out, I just use this.
  //
  if (target > stack.size ()) target = stack.size ();

  PHASE ("reduce", stats.reductions, "reducing %zd clauses %.0f%%",
    target, percent (target, stats.current.redundant));

  auto i = stack.begin ();
  const auto t = i + target;
  while (i != t) {
    Clause * c = *i++;
    LOG (c, "marking useless to be collected");
    mark_garbage (c);
    stats.reduced++;
  }

  lim.keptsize = lim.keptglue = 0;

  const auto end = stack.end ();
  for (i = t; i != end; i++) {
    Clause * c = *i;
    LOG (c, "keeping");
    if (c->size > lim.keptsize) lim.keptsize = c->size;
    if (c->glue > lim.keptglue) lim.keptglue = c->glue;
  }

  erase_vector (stack);

  PHASE ("reduce", stats.reductions,
    "maximum kept size %d glue %d", lim.keptsize, lim.keptglue);
}

/*------------------------------------------------------------------------*/

// If chronological backtracking produces out-of-order assigned units, then
// it is necessary to completely propagate them at the root level in order
// to derive all implied units.  Otherwise the blocking literals in
// 'flush_watches' are messed up and assertion 'FW1' fails.

bool Internal::propagate_out_of_order_units () {
  if (!level) return true;
  int oou = 0;
  for (size_t i = control[1].trail; !oou && i < trail.size (); i++) {
    const int lit = trail[i];
    assert (val (lit) > 0);
    if (var (lit).level) continue;
    LOG ("found out-of-order assigned unit %d", oou);
    oou = lit;
  }
  if (!oou) return true;
  assert (opts.chrono);
  backtrack (0);
  if (propagate ()) return true;
  learn_empty_clause ();
  return false;
}

/*------------------------------------------------------------------------*/

void Internal::reduce () {
  START (reduce);

  stats.reductions++;
  report ('.', 1);

  bool flush = flushing ();
  if (flush) stats.flush.count++;

  if (!propagate_out_of_order_units ()) goto DONE;

  mark_satisfied_clauses_as_garbage ();
  protect_reasons ();
  if (flush) mark_clauses_to_be_flushed ();
  else mark_useless_redundant_clauses_as_garbage ();
  garbage_collection ();

  {
    int64_t delta = opts.reduceint * (stats.reductions + 1);
    if (irredundant () > 1e5) {
      delta *= log (irredundant ()/1e4) / log (10);
      if (delta < 1) delta = 1;
    }
    lim.reduce = stats.conflicts + delta;
    PHASE ("reduce", stats.reductions,
      "new reduce limit %" PRId64 " after %" PRId64 " conflicts",
      lim.reduce, delta);
  }

  if (flush) {
    PHASE ("flush", stats.flush.count,
      "new flush increment %" PRId64 "", inc.flush);
    inc.flush *= opts.flushfactor;
    lim.flush = stats.conflicts + inc.flush;
    PHASE ("flush", stats.flush.count,
      "new flush limit %" PRId64 "", lim.flush);
  }

  last.reduce.conflicts = stats.conflicts;

DONE:

  report (flush ? 'f' : '-');
  STOP (reduce);
}

}
