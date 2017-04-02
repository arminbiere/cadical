#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// On-the-fly (dynamic) hyper binary resolution on decision level one can
// make use of the fact that the implication graph is actually a tree.

// Compute a dominator of two literals in the binary implication tree.

int Internal::probe_dominator (int a, int b) {
  int l = a, k = b;
  Var * u = &var (l), * v = &var (k);
  assert (val (l) > 0), assert (val (k) > 0);
  assert (u->level == 1), assert (v->level == 1);
  while (l != k) {
    if (u->trail > v->trail) swap (l, k), swap (u, v);
    if (!u->parent) return l;
    int parent = v->parent;
    if (k < 0) parent = -parent;
    assert  (parent), assert (val (parent) > 0);
    v = &var (k = parent);
    assert (v->level == 1);
  }
  LOG ("dominator %d of %d and %d", l, a, b);
  assert (val (l) > 0);
  return l;
}

// The idea of dynamic on-the-fly hyper-binary resolution came up in the
// PrecoSAT, where it originally was used on all decision levels.

// It turned out, that most of the hyper-binary resolvents were generated
// during probing on decision level one anyhow.  Thus this version is
// specialized to decision level one, where actually all long (non-binary)
// forcing clauses can be resolved to become binary.  So if we find a clause
// which would force a new assignment at decision level one during probing
// we resolve it (the 'reason' argument) to obtain a hyper binary resolvent.
// It consists of the still unassigned literal (the new unit) and the
// negation of the unique closest dominator of the negation of all (false)
// literals in the clause (which has to exist on decision level).

// There are two special cases which should be mentioned:
//
//   (A) The reason is already a binary clause in a certain sense, since all
//   its unwatched literals are root level fixed to false.  In this
//   situation it would be better to shrink the clause immediately instead
//   of adding a new clause consisting only of the watched literals.
//   However, this would happen during the next garbage collection anyhow.
//
//   (B) The resolvent subsumes the original reason clause. This is
//   equivalent to the property that the negated dominator is contained in
//   the original reason.  Again one could in principle shrink the clause.
//
// Note that (A) is actually subsumed by (B).  The possible optimization to
// shrink the clause on-the-fly is difficult (need to update 'blit' and
// 'binary' of the other watch at least) and also not really that important.
// For (B) we simply add the new binary resolvent and mark the old subsumed
// clause as garbage instead.  And since in the situation of (A) the
// shrinking will be performed at the next  garbage collection anyhow, we
// do not change clauses in (A).

// The hyper binary resolvent clause is redundant unless it subsumes the
// original reason and that one is irredundant.

// If the option 'opts.hbr' is 'false', we actually do not add the new hyper
// binary resolvent, but simply pretend we would have added it and still
// return the dominator as new reason / parent for the new unit.

// Finally note that adding clauses changes the watches of the probagated
// literal and thus we can not use standard iterators during probing but
// need to fall back to indices.  One watch for the hyper binary resolvent
// clause is added at the end of the currently propagated watches, but its
// watch is a binary watch and will be skipped during propagating long
// clauses anyhow.

inline int Internal::hyper_binary_resolve (Clause * reason) {
  assert (level == 1);
  assert (reason->size > 2);
  const const_literal_iterator end = reason->end ();
  const int * lits = reason->literals;
  const_literal_iterator k;
#ifndef NDEBUG
  // First literal unassigned, all others false.
  assert (!val (lits[0]));
  for (k = lits + 1; k != end; k++) assert (val (*k) < 0);
  assert (var (lits[1]).level == 1);
#endif
  LOG (reason, "hyper binary resolving");
  stats.hbrs++;
  stats.hbrsizes += reason->size;
  const int lit = lits[1];
  int dom = -lit, non_root_level_literals = 0;
  for (k = lits + 2; k != end; k++) {
    const int other = -*k;
    assert (val (other) > 0);
    if (!var (other).level) continue;
    dom = probe_dominator (dom, other);
    non_root_level_literals++;
  }
  if (non_root_level_literals && // !(A)
      opts.hbr && reason->size <= opts.hbrsizelim) {
    bool contained = false;
    for (k = lits + 1; !contained && k != end; k++)
      contained = (*k == -dom);
    const bool red = !contained || reason->redundant;
    if (red) stats.hbreds++;
    LOG ("new %s hyper binary resolvent %d %d",
      (red ? "redundant" : "irredundant"), -dom, lits[0]);
    assert (clause.empty ());
    clause.push_back (-dom);
    clause.push_back (lits[0]);
    external->check_learned_clause ();
    Clause * c = new_hyper_binary_resolved_clause (red, 2);
    if (red) c->hbr = true;
    clause.clear ();
    if (contained) {
      stats.hbrsubs++;
      LOG (reason, "subsumed original");
      mark_garbage (reason);
    }
  }
  return dom;
}

/*------------------------------------------------------------------------*/

// The following functions 'probe_assign' and 'probagate' are used for
// propagating (note the 'b') during failed literal probing in
// simplification mode, as replacement of the generic propagation routine
// 'propagate' and 'search_assign'.

// The code is mostly copied from 'propagate.cpp' and specialized.  We only
// comment on the differences.  More explanations are in 'propagate.cpp'.

inline void Internal::probe_assign (int lit, int parent) {
  assert (simplifying);
  int idx = vidx (lit);
  assert (!vals[idx]);
  assert (!flags (idx).eliminated () || !parent);
  assert (!parent || val (parent) > 0);
  Var & v = var (idx);
  v.level = level;
  v.trail = (int) trail.size ();
  const signed char tmp = sign (lit);
  v.parent = tmp < 0 ? -parent : parent;
  if (!level) learn_unit_clause (lit);
  else assert (level == 1);
  vals[idx] = tmp;
  vals[-idx] = -tmp;
  assert (val (lit) > 0);
  assert (val (-lit) < 0);
  // no phase saving here ...
  propfixed (lit) = stats.all.fixed;
  trail.push_back (lit);
  if (parent) LOG ("assign %d parent %d", lit, parent);
  else if (level) LOG ("assign %d probe", lit);
  else LOG ("assign %d negated failed literal UIP", lit);
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
// always propagate binary clauses first (see our CPAIOR paper on tree based
// look ahead), then immediately stop at a conflict and of course use
// 'probe_assign' instead of 'search_assign'.  The binary propagation part
// is factored out too.  If a new unit on decision level one is found we
// perform hyper binary resolution and thus actually build an implication
// tree instead of a DAG.  Statistics counters are also different.

void Internal::probagate2 () {
  while (!conflict && probagated2 < trail.size ()) {
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
      else probe_assign (w.blit, -lit);
    }
  }
}

bool Internal::probagate () {

  assert (simplifying);
  assert (!unsat);

  START (propagate);

  long before = probagated2;

  while (!conflict) {
    if (probagated2 < trail.size ()) probagate2 ();
    else if (probagated < trail.size ()) {
      const int lit = -trail[probagated++];
      LOG ("probagating %d over large clauses", -lit);
      Watches & ws = watches (lit);
      size_t i = 0, j = 0;
      while (i != ws.size ()) {
        const Watch w = ws[j++] = ws[i++];
        if (w.binary) continue;
        const int b = val (w.blit);
        if (b > 0) continue;
        if (w.clause->garbage) continue;
        literal_iterator lits = w.clause->begin ();
	const int other = lits[0]^lits[1]^lit;
	lits[0] = other, lits[1] = lit;
        const int u = val (other);
        if (u > 0) ws[j-1].blit = other;
        else {
          const int size = w.clause->size;
          const const_literal_iterator end = lits + size;
          literal_iterator k;
          int v = -1, r = 0;
	  if (w.clause->extended) {
	    const literal_iterator start = lits + w.clause->pos ();
	    k = start;
	    while (k != end && (v = val (r = *k)) < 0) k++;
            if (v < 0) {
              const const_literal_iterator middle = lits + w.clause->pos ();
              k = lits + 2;
              assert (w.clause->pos () <= size);
              while (k != middle && (v = val (r = *k)) < 0) k++;
            }
            w.clause->pos () = k - lits;
          } else {
	    const literal_iterator start = lits + 2;
	    k = start;
	    while (k != end && (v = val (r = *k)) < 0) k++;
	  }
          assert (lits + 2 <= k), assert (k <= w.clause->end ());
          if (v > 0) ws[j-1].blit = r;
          else if (!v) {
            LOG (w.clause, "unwatch %d in", r);
	    *k = lit;
	    lits[1] = r;
            watch_literal (r, lit, w.clause, size);
            j--;
          } else if (!u) {
            if (level == 1) {
              int dom = hyper_binary_resolve (w.clause);
              probe_assign (other, dom);
            } else probe_assign_unit (other);
	    probagate2 ();
          } else { conflict = w.clause; break; }
        }
      }
      if (j < i) {
	while (i != ws.size ()) ws[j++] = ws[i++];
	ws.resize (j);
      }
    } else break;
  }
  long delta = probagated2 - before;
  stats.propagations.probe += delta;
  if (conflict) LOG (conflict, "conflict");
  STOP (propagate);
  return !conflict;
}

};
