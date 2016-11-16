#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"

namespace CaDiCaL {

bool Internal::probing () {
  if (!opts.probe) return false;
  return lim.probe <= stats.conflicts;
}

bool Internal::occurs_in_binary_clauses (int lit) {
  const Watches & ws = watches (lit);
  const const_watch_iterator end = ws.end ();
  const_watch_iterator i;
  for (i = ws.begin (); i != end; i++)
    if (i->size == 2) return true;
  return false;
}

void Internal::probe () {

  SWITCH_AND_START (search, simplify, probe);

  assert (!simplifying);
  simplifying = true;
  stats.probings++;

  int old_failed = stats.failed;
  long old_probed = stats.probed;

  backtrack ();

  int * stamp;
  NEW (stamp, int, 2*(max_var + 1));
  ZERO (stamp, int, 2*(max_var + 1));
  stamp += max_var;

  for (int idx = 1; !unsat && idx <= max_var; idx++) {
    if (val (idx)) continue;
    if (eliminated (idx)) continue;
    bool pos_prop_no_fail = stamp[idx] < stats.failed;
    bool neg_prop_no_fail = stamp[-idx] < stats.failed;
    if (!pos_prop_no_fail && !neg_prop_no_fail) continue;
    bool pos_bin_occs = occurs_in_binary_clauses (idx);
    bool neg_bin_occs = occurs_in_binary_clauses (-idx);
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
