#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"

namespace CaDiCaL {

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
  if (f.seen ()) return;
  if (!var (lit).level) return;
  f.set (SEEN);
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

void Internal::failed_literal (int failed) {

  LOG ("analyzing failed literal probe %d", failed);
  stats.failed++;

  assert (!unsat);
  assert (conflict);
  assert (level == 1);
  assert (control[1].decision == failed);
  assert (seen.empty ());

  START (analyze);

  Clause * reason = conflict;
  LOG (reason, "analyzing failed literal conflict");
  int open = 0, uip = 0, other = 0;
  const_int_iterator i = trail.end ();
  vector<int> uips;
  for (;;) {
    if (reason) analyze_failed_reason (uip, reason, open);
    else analyze_failed_literal (other, open);
    while (!flags (uip = *--i).seen ())
      ;
    if (!--open) {
      LOG ("%ld. UIP %d", (long) units.size (), uip);
      uips.push_back (uip);
    }
    Var & v = var (uip);
    if (v.decision ()) break;
    if (!(reason = v.reason)) other = v.other;
#ifdef LOGGING
    if (reason) LOG (reason, "analyzing %d reason", uip);
    else LOG ("analyzing %d binary reason %d %d", uip, uip, other);
#endif
  }
  LOG ("found %ld UIPs", (long) uips.size ());
  assert (!uips.empty ());

  backtrack ();
  clear_seen ();
  conflict = 0;

  const const_int_iterator end = uips.end ();
  for (const_int_iterator i = uips.begin (); i != end; i++)
    assign (-*i);

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

  signed char * bins;
  NEW (bins, signed char, 2*(max_var + 1));
  ZERO (bins, signed char, 2*(max_var + 1));
  bins += max_var;

  const const_clause_iterator end = clauses.end ();
  const_clause_iterator i;
  for (i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    if (c->size != 2) continue;
    bins[c->literals[0]] = 1;
    bins[c->literals[1]] = 1;
  }

  for (int idx = 1; !unsat && idx <= max_var; idx++) {
    if (val (idx)) continue;
    if (eliminated (idx)) continue;
    bool pos_prop_no_fail = fixedprop (idx) < stats.fixed;
    bool neg_prop_no_fail = fixedprop (-idx) < stats.fixed;
    if (!pos_prop_no_fail && !neg_prop_no_fail) continue;
    bool pos_bin_occs = bins[idx];
    bool neg_bin_occs = bins[-idx];
    if (pos_bin_occs == neg_bin_occs) continue;
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
    size_t before_propagation = trail.size ();
    assume_decision (decision);
    if (propagate ()) {
      for (size_t i = before_propagation; i < trail.size (); i++)
	fixedprop (trail[i]) = stats.fixed;
      backtrack ();
    } else failed_literal (decision);
  }

  bins -= max_var;
  DEL (bins, signed char, 2*(max_var + 1));

  int failed = stats.failed - old_failed;
  long probed = stats.probed - old_probed;

  VRB ("probe", stats.probings, 
    "probed %ld and found %d failed literals",
    probed, failed);

  assert (simplifying);
  simplifying = false;

  if (failed) inc.probe *= 2;
  else inc.probe += opts.probeint;
  lim.probe = stats.conflicts + inc.probe;

  report ('p');

  STOP_AND_SWITCH (probe, simplify, search);
}

};
