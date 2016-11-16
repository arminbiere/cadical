#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"

namespace CaDiCaL {

bool Internal::probing () {
  if (!opts.probe) return false;
  return lim.probe <= stats.conflicts;
}

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

  int * stamp;
  NEW (stamp, int, 2*(max_var + 1));
  stamp += max_var;
  for (int lit = -max_var; lit <= max_var; lit++) stamp[lit] = -1;

  for (int idx = 1; !unsat && idx <= max_var; idx++) {
    if (val (idx)) continue;
    if (eliminated (idx)) continue;
    bool pos_prop_no_fail = stamp[idx] < stats.failed;
    bool neg_prop_no_fail = stamp[-idx] < stats.failed;
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
	stamp[trail[i]] = stats.failed;
      backtrack ();
    } else {
      stats.failed++;
      analyze ();
      assert (!level);
      if (propagate ()) continue;
      learn_empty_clause ();
      assert (unsat);
    }
  }

  stamp -= max_var;
  DEL (stamp, int, 2*(max_var + 1));

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
