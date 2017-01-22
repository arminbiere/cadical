#include "internal.hpp"

namespace CaDiCaL {

// Failed literal probing in phases.

bool Internal::probing () {

  if (!opts.simplify) return false;
  if (!opts.probe) return false;

  // Wait until next 'reduce'.
  //
  if (stats.conflicts != lim.conflicts_at_last_reduce) return false;

  return lim.probe <= stats.conflicts;
}

/*------------------------------------------------------------------------*/

// This a specialized instance of 'analyze'.

void Internal::failed_literal (int failed) {

  LOG ("analyzing failed literal probe %d", failed);
  stats.failed++;

  assert (!unsat);
  assert (conflict);
  assert (level == 1);
  assert (analyzed.empty ());

  START (analyze);

  LOG (conflict, "analyzing failed literal conflict");

  const const_literal_iterator end = conflict->end ();
  const_literal_iterator i;
  int uip = 0;
  for (i = conflict->begin (); i != end; i++) {
    const int other = -*i;
    if (!var (other).level) continue;
    uip = uip ? probe_dominator (uip, other) : other;
  }
  LOG ("found probing UIP %d", uip);
  assert (uip);

  vector<int> parents;
  int parent = uip;
  while (parent != failed) {
    int next = var (parent).parent;
    if (parent < 0) next = -next;
    parent = next;
    assert (parent);
    parents.push_back (parent);
  }

  packtrack (failed);
  clear_seen ();
  conflict = 0;

  assert (!val (uip));
  probe_assign_unit (-uip);

  if (!probagate ()) learn_empty_clause ();

  while (!unsat && !parents.empty ()) {
    const int parent = parents.back ();
    parents.pop_back ();
    const int tmp = val (parent);
    if (tmp < 0) continue;
    if (tmp > 0) {
      LOG ("clashing failed parent %d", parent);
      learn_empty_clause ();
    } else {
      LOG ("found unassigned failed parent %d", parent);
      probe_assign_unit (-parent);
      if (!probagate ()) learn_empty_clause ();
    }
  }
  erase_vector (parents);

  STOP (analyze);

  assert (unsat || val (failed) < 0);
}

/*------------------------------------------------------------------------*/

struct less_negated_occs {
  Internal * internal;
  less_negated_occs (Internal * i) : internal (i) { }
  bool operator () (int a, int b) {
    long l = internal->noccs (-a);
    long k = internal->noccs (-b);
    if (l < k) return true;
    if (l > k) return false;
    assert (a != -b);
    return abs (a) > abs (b);
  }
};

void Internal::generate_probes () {

  assert (probes.empty ());

  // First determine all the literals which occur in binary clauses. It is
  // way faster to go over the clauses once, instead of walking the watch
  // lists for each literal.
  //
  init_noccs ();
  const const_clause_iterator end = clauses.end ();
  const_clause_iterator i;
  for (i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    if (c->size != 2) continue;
    noccs (c->literals[0])++;
    noccs (c->literals[1])++;
  }

  for (int idx = 1; idx <= max_var; idx++) {
    // Then focus on roots of the binary implication graph, which are
    // literals which occur negatively in a binary clause, but not
    // positively.  If neither 'idx' nor '-idx' is a root it does not make
    // sense to probe this variable.  This assumes that equivalent literal
    // substitution was performed.
    //
    bool have_pos_bin_occs = noccs (idx) > 0;
    bool have_neg_bin_occs = noccs (-idx) > 0;
    if (have_pos_bin_occs == have_neg_bin_occs) continue;
    int probe = have_neg_bin_occs ? idx : -idx;
    LOG ("scheduling probe %d negated occs %ld", noccs (-probe));
    probes.push_back (probe);
  }

  sort (probes.begin (), probes.end (), less_negated_occs (this));

  reset_noccs ();
  shrink_vector (probes);

  if (probes.empty ()) LOG ("no potential probes found");
  else LOG ("new probes schedule of size %ld", (long) probes.size ());
}

int Internal::next_probe () {
  int generated = 0;
  for (;;) {
    if (probes.empty ()) {
      if (generated++) return 0;
      generate_probes ();
    }
    while (!probes.empty ()) {
      int probe = probes.back ();
      probes.pop_back ();
      if (!active (probe)) continue;
      if (propfixed (probe) < stats.all.fixed) return probe;
    }
  }
}

void Internal::probe_core () {
  assert (!simplifying);
  simplifying = true;

  stats.probings++;

  int old_failed = stats.failed;
#ifndef QUIET
  long old_probed = stats.probed;
#endif

  assert (unsat || propagated == trail.size ());
  probagated = probagated2 = trail.size ();

  // Probing is limited in terms of non-probing propagations
  // 'stats.propagations'. We allow a certain percentage 'opts.probereleff'
  // (say %5) of probing propagations (called 'probagations') in each
  // probing with a lower bound of 'opts.probmineff'.
  //
  long delta = stats.propagations.search;
  delta -= lim.search_propagations.probe;
  delta *= opts.probereleff;
  if (delta < opts.probemineff) delta = opts.probemineff;
  if (delta > opts.probemaxeff) delta = opts.probemaxeff;
  long limit = stats.propagations.probe + delta;

  int probe;
  while (!unsat &&
         stats.propagations.probe < limit &&
         (probe = next_probe ())) {
    stats.probed++;
    LOG ("probing %d", probe);
    level++;
    probe_assign_decision (probe);
    if (probagate ()) packtrack (probe);
    else failed_literal (probe);
  }

  assert (simplifying);
  simplifying = false;

  if (unsat) LOG ("probing derived empty clause");
  else if (propagated < trail.size ()) {
    LOG ("probing produced %ld units", trail.size () - propagated);
    if (!propagate ()) {
      LOG ("propagating units after probing results in empty clause");
      learn_empty_clause ();
    } else sort_watches ();
  }

  int failed = stats.failed - old_failed;
#ifndef QUIET
  long probed = stats.probed - old_probed;
#endif

  if (!failed) inc.probe *= 2;
  else inc.probe += opts.probeint;
  lim.probe = stats.conflicts + inc.probe;

  lim.search_propagations.probe = stats.propagations.search;

  VRB ("probe", stats.probings,
    "probed %ld and found %d failed literals",
    probed, failed);

  report ('p');
}

void CaDiCaL::Internal::probe () {
  SWITCH_AND_START (search, simplify, probe);
  if (level) backtrack ();
  assert (!unsat);
  decompose ();
  if (!unsat) {
    mark_duplicated_binary_clauses_as_garbage ();
    probe_core ();
    if (!unsat) decompose ();
  }
  STOP_AND_SWITCH (probe, simplify, search);
}

};
