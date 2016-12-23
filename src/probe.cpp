#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"

namespace CaDiCaL {

// Failed literal probing in phases.

bool Internal::probing () {
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

struct less_negated_bins {
  Internal * internal;
  long * bins;
  less_negated_bins (Internal * i, long * b) : internal (i), bins (b) { }
  bool operator () (int a, int b) {
    long l = bins [internal->vlit (-a)], k = bins [internal->vlit (-b)];
    if (l < k) return true;
    if (l > k) return false;
    assert (a != -b);
    return abs (a) > abs (b);
  }
};

void Internal::generate_probes () {

  assert (probes.empty ());

  // First determine all the literals which occur in binary clauses. It is
  // way faster. To go over the clauses once, instead of walking the watch
  // lists for each literal.
  //
  long * bins;
  NEW (bins, long, 2*(max_var + 1));
  ZERO (bins, long, 2*(max_var + 1));
  const const_clause_iterator end = clauses.end ();
  const_clause_iterator i;
  for (i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    if (c->size != 2) continue;
    bins[vlit (c->literals[0])]++;
    bins[vlit (c->literals[1])]++;
  }

  for (int idx = 1; idx <= max_var; idx++) {
    // Then focus on roots of the binary implication graph, which are
    // literals which occur negatively in a binary clause, but not
    // positively.  If neither 'idx' nor '-idx' is a root it does not make
    // sense to probe this variable.  This assumes that equivalent literal
    // substitution was performed.
    //
    bool have_pos_bin_occs = bins[vlit (idx)] > 0;
    bool have_neg_bin_occs = bins[vlit (-idx)] > 0;
    if (have_pos_bin_occs == have_neg_bin_occs) continue;
    int probe = have_neg_bin_occs ? idx : -idx;
    LOG ("scheduling probe %d", probe);
    probes.push_back (probe);
  }

  sort (probes.begin (), probes.end (), less_negated_bins (this, bins));

  DEL (bins, long, 2*(max_var + 1));
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
      if (propfixed (probe) < stats.fixed) return probe;
    }
  }
}

void Internal::probe_core () {
  assert (!simplifying);
  simplifying = true;

  stats.probings++;

  int old_failed = stats.failed;
  long old_probed = stats.probed;

  assert (unsat || propagated == trail.size ());
  probagated = probagated2 = trail.size ();

  // After an arithmetic increasing number of calls to 'probe_core' we
  // reschedule all roots of the binary implication graph, instead of only
  // those not tried before.  Then this limit is increased by one. The
  // argument is that we should focus on those roots with many occurrences
  // in binary clauses of their negated literals but in the limit eventually
  // still should probe all roots.
  //
  if (!lim.probe_wait_reschedule) {
    VRB ("probe", stats.probings, "forced to reschedule all probes");
    lim.probe_wait_reschedule = ++inc.probe_wait_reschedule;
    probes.clear ();
  } else lim.probe_wait_reschedule--;

  // Probing is limited in terms of non-probing propagations
  // 'stats.propagations'. We allow a certain percentage 'opts.probereleff'
  // (say %5) of probing propagations (called 'probagations') in each
  // probing with a lower bound of 'opts.probmineff'.
  //
  long delta = opts.probereleff * stats.propagations.search;
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
  long probed = stats.probed - old_probed;

  if (!failed) inc.probe *= 2;
  else inc.probe += opts.probeint;
  lim.probe = stats.conflicts + inc.probe;

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
