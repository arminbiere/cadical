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
  assert (control[1].decision == failed);
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

  backtrack ();
  clear_seen ();
  conflict = 0;

  const const_int_iterator end = uips.end ();
  for (const_int_iterator i = uips.begin (); i != end; i++)
    assign_unit (-*i);

  STOP (analyze);

  if (!propagate ()) learn_empty_clause ();

  assert (unsat || val (failed) < 0);
}

/*------------------------------------------------------------------------*/

void Internal::probe () {

  SWITCH_AND_START (search, simplify, probe);

  assert (!simplifying);
  simplifying = true;
  stats.probings++;

  int old_failed = stats.failed;
  long old_probed = stats.probed;

  backtrack ();

  // First determine all the literals which occur in binary clauses. It is
  // way faster. To go over the clauses once, instead of walking the watch
  // lists for each literal.
  //
  signed char * bins;
  NEW (bins, signed char, 2*(max_var + 1));
  ZERO (bins, signed char, 2*(max_var + 1));
  const const_clause_iterator end = clauses.end ();
  const_clause_iterator i;
  for (i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    if (c->size != 2) continue;
    bins[vlit (c->literals[0])] = 1;
    bins[vlit (c->literals[1])] = 1;
  }

  // Probing is limited in terms of non-probing propagations
  // 'stats.propagations'. We allow a certain percentage 'opts.probereleff'
  // (say %5) of probing propagations (called 'probagations') in each
  // probing with a lower bound of 'opts.probmineff'.
  //
  long delta = opts.probereleff * stats.propagations;
  if (delta < opts.probemineff) delta = opts.probemineff;
  long limit = stats.probagations + delta;

  // We have a persistent variable index iterator to schedule probes, which
  // starts from the last variable index tried before and wraps around at
  // 'max_var' until the first variable index is reached or the probing
  // limit is hit.  The next to last probe tried is saved and will be used
  // as starting point for the next probing round.
  //
  VarIdxIterator it (lim.last_probed, max_var);
  int idx;

  while (!unsat && stats.probagations < limit && (idx = it.next ())) {

    if (!active (idx)) continue;

    // First check whether there was a new unit learned since the last time
    // either 'idx' or '-idx' where propagated.  If both were propagated
    // without producing a unit and no new unit has been learned since then,
    // there is no need to consider 'idx' as probe.  Note that 'fixedprop'
    // also takes propagations during regular CDCL search into account.
    //
    bool pos_prop_no_fail = fixedprop (idx) < stats.fixed;
    bool neg_prop_no_fail = fixedprop (-idx) < stats.fixed;
    if (!pos_prop_no_fail && !neg_prop_no_fail) continue;

    // Then focus on roots of the binary implication graph, which are
    // literals which occur negatively in a binary clause, but not
    // positively.  If neither 'idx' nor '-idx' is a root it does not make
    // sense to probe this variable.  This assumes that equivalent literal
    // substitution was performed.
    //
    bool pos_bin_occs = bins[vlit (idx)];
    bool neg_bin_occs = bins[vlit (-idx)];
    if (pos_bin_occs == neg_bin_occs) continue;

    // First try the phase in which the variable is a root unless that
    // literal was propagated since the last found unit without success.
    //
    int decision;
    if (pos_bin_occs) {
      assert (!neg_bin_occs);
      if (!neg_prop_no_fail) continue;
      decision = -idx;
    } else {
      assert (neg_bin_occs);
      if (!pos_prop_no_fail) continue;
      decision = idx;
    } 

    LOG ("probing %d", decision);
    stats.probed++;
    assume_decision (decision);
    if (propagate ()) backtrack ();
    else failed_literal (decision);
  }

  DEL (bins, signed char, 2*(max_var + 1));

  int failed = stats.failed - old_failed;
  long probed = stats.probed - old_probed;

  VRB ("probe", stats.probings, 
    "probed %ld and found %d failed literals",
    probed, failed);

  assert (simplifying);
  simplifying = false;

  if (!failed) inc.probe *= 2;
  else inc.probe += opts.probeint;
  lim.probe = stats.conflicts + inc.probe;

  report ('p');

  STOP_AND_SWITCH (probe, simplify, search);
}

};
