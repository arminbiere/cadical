#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"

namespace CaDiCaL {

// Failed literal probing in phases.

bool Internal::probing () {
  if (!opts.probe) return false;
  return lim.probe <= stats.conflicts;
}

/*------------------------------------------------------------------------*/

// These are optimized versions of the corresponding 'analyze_literal' and
// 'analyze_reason' functions in 'analyze.cpp' for the case 'level == 1'.

inline void Internal::analyze_failed_literal (int lit, int & open) {
  assert (lit);
  Flags & f = flags (lit);
  if (f.seen) return;
  if (!var (lit).level) return;
  f.seen = true;
  analyzed.push_back (lit);
  LOG ("analyzed failed literal %d", lit);
  open++;
}

inline void
Internal::analyze_failed_reason (int lit, Clause * reason, int & open) {
  assert (reason);
  const const_literal_iterator end = reason->end ();
  const_literal_iterator j = reason->begin ();
  int other;
  while (j != end)
    if ((other = *j++) != lit)
      analyze_failed_literal (other, open);
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

  Clause * reason = conflict;
  LOG (reason, "analyzing failed literal conflict");
  int open = 0, uip = 0, other = 0;
  const_int_iterator i = trail.end ();
  vector<int> uips;
  for (;;) {
    if (reason) analyze_failed_reason (uip, reason, open);
    else analyze_failed_literal (other, open);
    while (!flags (uip = *--i).seen)
      ;
    if (!--open) {
      LOG ("%ld. UIP %d", (long) uips.size (), uip);
      uips.push_back (uip);
    }
    if (!(reason = var (uip).reason)) break;
    LOG (reason, "analyzing %d reason", uip);
  }
  LOG ("found %ld UIPs", (long) uips.size ());
  assert (!uips.empty ());

  packtrack (failed);
  clear_seen ();
  conflict = 0;

  const const_int_iterator end = uips.end ();
  for (const_int_iterator i = uips.begin (); i != end; i++)
    probe_assign_unit (-*i);

  STOP (analyze);

  if (!probagate ()) learn_empty_clause ();

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

void Internal::probe () {

  SWITCH_AND_START (search, simplify, probe);

  if (level) backtrack ();

  assert (!simplifying);
  simplifying = true;
  stats.probings++;

  int old_failed = stats.failed;
  long old_probed = stats.probed;

  assert (propagated == trail.size ());
  probagated = probagated2 = trail.size ();

  init_doms ();

  // Probing is limited in terms of non-probing propagations
  // 'stats.propagations'. We allow a certain percentage 'opts.probereleff'
  // (say %5) of probing propagations (called 'probagations') in each
  // probing with a lower bound of 'opts.probmineff'.
  //
  long delta = opts.probereleff * stats.propagations;
  if (delta < opts.probemineff) delta = opts.probemineff;
  long limit = stats.probagations + delta;

  int probe;
  while (!unsat && stats.probagations < limit && (probe = next_probe ())) {
    stats.probed++;
    LOG ("probing %d", probe);
    level++;
    probe_assign_decision (probe);
    if (probagate ()) packtrack (probe);
    else failed_literal (probe);
  }

  reset_doms ();

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

  STOP_AND_SWITCH (probe, simplify, search);
}

};
