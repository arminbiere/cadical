#include "internal.hpp"
#include "macros.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// On-the-fly (dynamic) hyper binary resolution.

int Internal::probe_dominator (int a, int b) {
  int l = a, k = b;
  while (l != k) {
    assert (val (l) > 0), assert (val (k) > 0);
    Var * u = &var (l), * v = &var (k);
    assert (u->level > 0), assert (v->level > 0);
    if (u->trail > v->trail) swap (l, k), swap (u, v);
    if (!u->reason) return l;
    Clause * c = v->reason;
    assert (c);
    const const_literal_iterator end = c->end ();
    const_literal_iterator i;
    int pred = 0;
#if 0
    for (i = c->begin (); !pred && i != end; i++) {
#else
    for (i = c->begin (); i != end; i++) {
#endif
      const int other = *i;
      if (other == k) continue;
      if (!var (other).level) continue;
      assert (!pred);
      pred = -other;
    }
    assert (pred);
    k = pred;
  }
  LOG ("dominator %d of %d and %d", l, a, b);
  return l;
}

Clause * Internal::hyper_binary_resolve (Clause * reason) {
  LOG (reason, "hyper binary resolving");
  assert (level == 1);
  stats.hbrs++;
  const int * lits = reason->literals;
  const int lit = lits[1];
  bool contained = true;
  int dom = -lit;
  Clause * res;
  const const_literal_iterator end = reason->end ();
  const_literal_iterator k;
  for (k = lits + 2; k != end; k++) {
    const int other = -*k;
    assert (val (other) > 0);
    if (!var (other).level) continue;
    dom = probe_dominator (dom, other);
    contained = (dom == other);
  }
  const bool red = !contained || reason->redundant;
  LOG ("new %s hyper binary resolvent %d %d", 
    (red ? "redundant" : "irredundant"), -dom, lits[0]);
  assert (clause.empty ());
  clause.push_back (-dom);
  clause.push_back (lits[0]);
  check_learned_clause ();
  res = new_hyper_binary_resolved_clause (red, 2);
  clause.clear ();
  if (contained) { 
    LOG (reason, "subsumed original");
    mark_garbage (reason);
  }
  return res;
}

/*------------------------------------------------------------------------*/

// The following functions 'probe_assign' are used for probagating (note the
// 'b') during failed literal probing in simplification mode, as replacement
// of the generic propagation routine 'propagate' and 'search_assign'.

// The code is mostly copied from 'propagate.cpp' and specialized.  We only
// comment on the differences.  More explanations are in 'propagate.cpp'.

inline void Internal::probe_assign (int lit, Clause * reason) {
  assert (simplifying);
  int idx = vidx (lit);
  assert (!vals[idx]);
  assert (!flags (idx).eliminated || !reason);
  Var & v = var (idx);
  v.level = level;
  v.trail = (int) trail.size ();
  v.reason = reason;
  if (!level) learn_unit_clause (lit);
  const signed char tmp = sign (lit);
  vals[idx] = tmp;
  vals[-idx] = -tmp;
  assert (val (lit) > 0);
  assert (val (-lit) < 0);
  // no phase saving here ...
  propfixed (lit) = stats.fixed;
  trail.push_back (lit);
  LOG (reason, "assign %d", lit);
  assert (watches ());
  if (opts.prefetch)
    __builtin_prefetch (&*(watches (-lit).begin ()));
}

void Internal::probe_assign_decision (int lit) {
  assert (level == 1);
  probe_assign (lit, 0);
}

void Internal::probe_assign_unit (int lit) {
  assert (!level);
  assert (active (lit));
  probe_assign (lit, 0);
}

/*------------------------------------------------------------------------*/

// This is essentially the same as 'propagate' except that we prioritize and
// always propagated binary clauses first (see our CPAIOR paper on tree
// based look ahead), stop at a conflict and of course use 'probe_assign'
// instead of 'search_assign'.  Statistics counters are also different.

bool Internal::probagate () {

  assert (simplifying);
  assert (!unsat);

  START (probagate);

  long before = probagated2;

  while (!conflict) {
    if (probagated2 < trail.size ()) {
      const int lit = -trail[probagated2++];
      LOG ("probagating %d over binary clauses", -lit);
      Watches & ws = watches (lit);
      const_watch_iterator i = ws.begin ();
      watch_iterator j = ws.begin ();
      while (!conflict && i != ws.end ()) {
        const Watch w = *j++ = *i++;
        if (!w.binary) continue;
        const int b = val (w.blit);
        if (b > 0) continue;
        if (b < 0) conflict = w.clause;
        else probe_assign (w.blit, w.clause);
      }
    } else if (probagated < trail.size ()) {
      const int lit = -trail[probagated++];
      LOG ("probagating %d over large clauses", -lit);
      Watches & ws = watches (lit);
      const_watch_iterator i = ws.begin ();
      watch_iterator j = ws.begin ();
      while (i != ws.end ()) {
        const Watch w = *j++ = *i++;
        if (w.binary) continue;
        const int b = val (w.blit);
        if (b > 0) continue;
        if (w.clause->garbage) continue;
        literal_iterator lits = w.clause->begin ();
        if (lits[0] == lit) swap (lits[0], lits[1]);
        assert (lits[1] == lit);
        const int u = val (lits[0]);
        if (u > 0) j[-1].blit = lits[0];
        else {
          const int size = w.clause->size;
          const const_literal_iterator end = lits + size;
          const bool have_pos = w.clause->have.pos;
          literal_iterator k;
          int v = -1;
          literal_iterator start = lits;
          start += have_pos ? w.clause->pos () : 2;
          k = start;
          while (k != end && (v = val (*k)) < 0) k++;
          if (have_pos) {
            if (v < 0) {
              const const_literal_iterator middle = lits + w.clause->pos ();
              k = lits + 2;
              assert (w.clause->pos () <= size);
              while (k != middle && (v = val (*k)) < 0) k++;
            }
            w.clause->pos () = k - lits;
          }
          assert (lits + 2 <= k), assert (k <= w.clause->end ());
          if (v > 0) j[-1].blit = *k;
          else if (!v) {
            LOG (w.clause, "unwatch %d in", *k);
            swap (lits[1], *k);
            watch_literal (lits[1], lit, w.clause, size);
            j--;
          } else if (!u) {
	    Clause * reason = w.clause;
	    if (level == 1) {
	      // If we assign a unit on decision level one through a long
	      // clause, then we can always perform a hyper binary
	      // resolution and use the resolvent binary reason as reason
	      // instead.  However, since we add a new clause, we have to be
	      // careful with our iterators, which have to be saved and
	      // restored.
	      //
	      size_t p = i - ws.begin (), q = i - ws.begin ();
	      reason = hyper_binary_resolve (w.clause);
	      i = ws.begin () + p, j = ws.begin () + q;
	    } else assert (!level);
	    probe_assign (lits[0], reason);
	  } else { conflict = w.clause; break; }
        }
      }
      while (i != ws.end ()) *j++ = *i++;
      ws.resize (j - ws.begin ());
    } else break;
  }
  long delta = probagated2 - before;
  stats.probagations += delta;
  if (conflict) LOG (conflict, "conflict");
  STOP (probagate);
  return !conflict;
}

};
