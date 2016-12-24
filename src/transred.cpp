#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"

namespace CaDiCaL {

void Internal::transred () {

  if (unsat) return;

  assert (opts.transred);
  SWITCH_AND_START (search, simplify, transred);
  stats.transreds++;

  const const_clause_iterator end = clauses.end ();
  const_clause_iterator i;

  // Find first clause not checked for being transitive yet.

  for (i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    if (c->size != 2) continue;
    if (c->redundant && c->hbr) continue;
    if (!c->transred) break;
  }

  if (i == end) {
    LOG ("rescheduling all clauses since no clauses to check left");
    for (i = clauses.begin (); i != end; i++) {
      Clause * c = *i;
      if (c->transred) c->transred = false;
    }
    i = clauses.begin ();
  }

  vector<int> work;

  long limit = opts.transredreleff * stats.propagations.search;
  if (limit < opts.transredmineff) limit = opts.transredmineff;
  if (limit > opts.transredmaxeff) limit = opts.transredmaxeff;

  long propagations = 0, units = 0, removed = 0;

  while (!unsat && i != end && propagations < limit) {
    Clause * c = *i++;
    if (c->garbage) continue;
    if (c->size != 2) continue;
    if (c->redundant && c->hbr) continue;
    if (c->transred) continue;
    c->transred = true;
    int src = -c->literals[0];
    int dst = c->literals[1];
    if (val (src) || val (dst)) continue;
    if (watches (src).size () > watches (dst).size ()) {
      int tmp = dst;
      dst = -src; src = -tmp;
    }
    const bool irredundant = !c->redundant;
    LOG (c, "checking transitive reduction of");
    assert (work.empty ());
    LOG ("searching path from %d to %d", src, dst);
    mark (src);
    work.push_back (src);
    size_t j = 0;
    bool transitive = false, failed = false;
    while (!transitive && !failed && j < work.size ()) {
      const int lit = work[j++];
      assert (marked (lit) > 0);
      LOG ("visiting %d", lit);
      propagations++;
      const Watches & ws = watches (-lit);
      const const_watch_iterator eow = ws.end ();
      const_watch_iterator k;
      for (k = ws.begin (); !transitive && !failed && k != eow; k++) {
	const Watch & w = *k;
	if (!w.binary) continue;
	Clause * d = w.clause;
	if (d == c) continue;
	assert (w.redundant == d->redundant);
	if (irredundant && w.redundant) continue;
	if (d->garbage) continue;
	const int other = w.blit;
	if (other == dst) transitive = true;
	else {
	  const int tmp = marked (other);
	  if (tmp > 0) continue;
	  else if (tmp < 0) {
	    LOG ("found both %d and %d reachable", -other, other);
	    failed = true;
	  } else {
	    mark (other);
	    work.push_back (other);
	  }
	}
      }
    }
    while (!work.empty ()) {
      const int lit = work.back ();
      work.pop_back ();
      unmark (lit);
    }
    if (transitive) {
      removed++;
      stats.transitive++;
      LOG (c, "transitive redundant");
      mark_garbage (c);
    } else if (failed) {
      units++;
      LOG ("found failed literal %d during transitive reduction", src);
      assign_unit (-src);
      if (!propagate ()) {
	LOG ("propagating new unit results in conflict");
	learn_empty_clause ();
      }
    }
  }

  stats.propagations.transred += propagations;
  erase_vector (work);

  VRB ("transred", stats.transreds,
    "removed %ld transitive clauses, found %d units",
    removed, units);

  report ('t');
  STOP_AND_SWITCH (transred, simplify, search);
}

};
