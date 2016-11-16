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

  stats.probings++;

  int old_failed = stats.failed;
  long old_probed = stats.probed;

  backtrack ();

  int failed = stats.failed - old_failed;
  long probed = stats.probed - old_probed;

  VRB ("probe", stats.probings, 
    "probed %ld and found %d failed literals",
    probed, failed);

  if (failed) inc.probe *= 2;
  else inc.probe += opts.probeint;
  lim.probe = stats.conflicts + inc.probe;

  report ('p');

  STOP_AND_SWITCH (probe, simplify, search);
}

};
