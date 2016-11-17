#include "internal.hpp"

#include "macros.hpp"
#include "message.hpp"
#include "util.hpp"

#include <cstring>
#include <cstdio>

namespace CaDiCaL {

Stats::Stats () { memset (this, 0, sizeof *this); }

void Stats::print (Internal * internal) {
  Stats & stats = internal->stats;
  double t = internal->seconds ();
  if (internal->opts.profile) internal->print_profile (t);
  size_t m = internal->max_bytes ();
  SECTION ("statistics");
  MSG ("probings:      %15ld   %10.2f    conflicts per probing",
    stats.probings, relative (stats.conflicts, stats.probings));
  MSG ("eliminations:  %15ld   %10.2f    conflicts per elimination",
    stats.eliminations, relative (stats.conflicts, stats.eliminations));
  MSG ("subsumptions:  %15ld   %10.2f    conflicts per subsumption",
    stats.subsumptions, relative (stats.conflicts, stats.subsumptions));
  MSG ("reductions:    %15ld   %10.2f    conflicts per reduction",
    stats.reductions, relative (stats.conflicts, stats.reductions));
  MSG ("restarts:      %15ld   %10.2f    conflicts per restart",
    stats.restarts, relative (stats.conflicts, stats.restarts));
  MSG ("conflicts:     %15ld   %10.2f    per second",
    stats.conflicts, relative (stats.conflicts, t));
  MSG ("decisions:     %15ld   %10.2f    per second",
    stats.decisions, relative (stats.decisions, t));
  long propagations = stats.propagations + stats.probagations;
  MSG ("propagations:  %15ld   %10.2f    millions per second",
    propagations, relative (propagations/1e6, t));
  MSG ("probagations:  %15ld   %10.2f %%  per propagation",
    stats.probagations, percent (stats.probagations, propagations));
  MSG ("probed:        %15ld   %10.2f    per failed",
    stats.probed, relative (stats.probed, stats.failed));
#ifdef STATS
  MSG ("  visits:      %15ld   %10.2f    per propagation",
    stats.visits, relative (stats.visits, stats.propagations));
  MSG ("  traversed:   %15ld   %10.2f    per visit",
    stats.traversed, relative (stats.traversed, stats.visits));
#endif
  MSG ("reused:        %15ld   %10.2f %%  per restart",
    stats.reused, percent (stats.reused, stats.restarts));
  MSG ("resolved:      %15ld   %10.2f    per eliminated",
    stats.resolved, relative (stats.resolved, stats.eliminated));
#ifndef STATS
  if (internal->opts.verbose) {
#endif
  MSG ("  resolved2:   %15ld   %10.2f %%  per resolved",
    stats.resolved2, percent (stats.resolved2, stats.resolved));
  MSG ("  restried:    %15ld   %10.2f %%  per resolved",
    stats.restried, percent (stats.restried, stats.resolved));
#ifndef STATS
  }
#endif
  MSG ("eliminated:    %15ld   %10.2f %%  of all variables",
    stats.eliminated, percent (stats.eliminated, internal->max_var));
  MSG ("failed:        %15ld   %10.2f %%  of all variables",
    stats.failed, percent (stats.failed, internal->max_var));
  MSG ("fixed:         %15ld   %10.2f %%  of all variables",
    stats.fixed, percent (stats.fixed, internal->max_var));
  MSG ("units:         %15ld   %10.2f    conflicts per unit",
    stats.units, relative (stats.conflicts, stats.units));
  MSG ("binaries:      %15ld   %10.2f    conflicts per binary",
    stats.binaries, relative (stats.conflicts, stats.binaries));
  MSG ("trailbumped:   %15ld   %10.2f %%  per conflict",
    stats.trailbumped, percent (stats.trailbumped, stats.conflicts));
  MSG ("analyzed:      %15ld   %10.2f    per conflict",
    stats.analyzed, relative (stats.analyzed, stats.conflicts));
  long learned = stats.learned - stats.minimized;
  MSG ("learned:       %15ld   %10.2f    per conflict",
    learned, relative (learned, stats.conflicts));
  MSG ("minimized:     %15ld   %10.2f %%  of 1st-UIP-literals",
    stats.minimized, percent (stats.minimized, stats.learned));
  MSG ("forward:       %15ld   %10.2f    tried per forward",
    stats.subsumed, relative (stats.subtried, stats.subsumed));
  MSG ("strengthened:  %15ld   %10.2f    per forward",
    stats.strengthened, relative (stats.strengthened, stats.subsumed));
  MSG ("shrunken:      %15ld   %10.2f %%  of tried literals",
    stats.shrunken, percent (stats.shrunken, stats.shrinktried));
  MSG ("backward:      %15ld   %10.2f %%  per conflict",
    stats.sublast, percent (stats.sublast, stats.conflicts));
#ifndef STATS
  if (internal->opts.verbose) {
#endif
    MSG ("  subirr:      %15ld   %10.2f %%  of subsumed",
      stats.subirr, percent (stats.subirr, stats.subsumed));
    MSG ("  subred:      %15ld   %10.2f %%  of subsumed",
      stats.subred, percent (stats.subred, stats.subsumed));
    MSG ("  subtried:    %15ld   %10.2f    per conflict",
      stats.subtried, relative (stats.subtried, stats.conflicts));
    MSG ("  subchecks:   %15ld   %10.2f    per tried",
      stats.subchecks, relative (stats.subchecks, stats.subtried));
    MSG ("  subchecks2:  %15ld   %10.2f %%  per subcheck",
      stats.subchecks2, percent (stats.subchecks2, stats.subchecks));
#ifndef STATS
  }
#endif
  MSG ("searched:      %15ld   %10.2f    per decision",
    stats.searched, relative (stats.searched, stats.decisions));
  MSG ("bumped:        %15ld   %10.2f    per conflict",
    stats.bumped, relative (stats.bumped, stats.conflicts));
  MSG ("reduced:       %15ld   %10.2f %%  clauses per conflict",
    stats.reduced, percent (stats.reduced, stats.conflicts));
  MSG ("collections:   %15ld   %10.2f    conflicts per collection",
    stats.collections, relative (stats.conflicts, stats.collections));
  MSG ("collected:     %15ld   %10.2f    bytes and MB",
    stats.collected, stats.collected/(double)(1l<<20));
  MSG ("maxbytes:      %15ld   %10.2f    bytes and MB",
    m, m/(double)(1l<<20));
  MSG ("time:          %15s   %10.2f    seconds", "", t);
  MSG ("");
}

};
