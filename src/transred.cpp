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

  vector<int> work;

  long units = 0, transitive = 0;

  for (i = clauses.begin (); !unsat && i != end; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    if (c->size != 2) continue;
    int src = -c->literals[0];
    int dst = c->literals[1];
    if (val (src) || val (dst)) continue;
    if (watches (src).size () > watches (dst).size ()) {
      int tmp = dst;
      dst = -src; src = -tmp;
    }
    if (c->redundant && c->hbr) continue;
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
      const Watches & ws = watches (-lit);
      const const_watch_iterator eow = ws.end ();
      const_watch_iterator k;
      for (k = ws.begin (); !transitive && !failed && k != eow; k++) {
	const Watch & w = *k;
	if (!w.binary) continue;
	Clause * d = w.clause;
	if (d == c) continue;
	if (d->garbage) continue;
	if (irredundant && d->redundant) continue;
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
      transitive++;
      stats.transitive++;
      LOG (c, "transitive redundant");
      mark_garbage (c);
      stats.transitive++;
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

  erase_vector (work);

  VRB ("transred", stats.transreds,
    "found %ld transitive clauses, found %d units",
    transitive, units);

  report ('t');
  STOP_AND_SWITCH (transred, simplify, search);
}

};
