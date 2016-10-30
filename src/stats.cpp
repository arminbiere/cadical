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
  MSG ("reductions:    %15ld   %10.2f    conflicts per reduction",
    stats.reductions, relative (stats.conflicts, stats.reductions));
  MSG ("restarts:      %15ld   %10.2f    conflicts per restart",
    stats.restarts, relative (stats.conflicts, stats.restarts));
  MSG ("conflicts:     %15ld   %10.2f    per second",
    stats.conflicts, relative (stats.conflicts, t));
  MSG ("decisions:     %15ld   %10.2f    per second",
    stats.decisions, relative (stats.decisions, t));
  MSG ("propagations:  %15ld   %10.2f    millions per second",
    stats.propagations, relative (stats.propagations/1e6, t));
  MSG ("reused:        %15ld   %10.2f %%  per restart",
    stats.reused, percent (stats.reused, stats.restarts));
  MSG ("units:         %15ld   %10.2f    conflicts per unit",
    stats.units, relative (stats.conflicts, stats.units));
  MSG ("binaries:      %15ld   %10.2f    conflicts per binary",
    stats.binaries, relative (stats.conflicts, stats.binaries));
  MSG ("reverse:       %15ld   %10.2f %%  per conflict",
    stats.reverse, percent (stats.reverse, stats.conflicts));
  MSG ("resolved:      %15ld   %10.2f    per conflict",
    stats.resolved, relative (stats.resolved, stats.conflicts));
  long learned = stats.learned - stats.minimized;
  MSG ("learned:       %15ld   %10.2f    per conflict",
    learned, relative (learned, stats.conflicts));
  MSG ("minimized:     %15ld   %10.2f %%  of 1st-UIP-literals",
    stats.minimized, percent (stats.minimized, stats.learned));
  MSG ("forward:       %15ld   %10.2f    tried per forward",
    stats.subsumed, relative (stats.subtried, stats.subsumed));
  MSG ("strengthened:  %15ld   %10.2f    per forward",
    stats.strengthened, relative (stats.strengthened, stats.subsumed));
  MSG ("shrunken:      %15ld   %10.2f    per conflict",
    stats.shrunken, relative (stats.shrunken, stats.conflicts));
  MSG ("backward:      %15ld   %10.2f %%  per conflict",
    stats.sublast, percent (stats.sublast, stats.conflicts));
  if (internal->opts.verbose) {
    MSG ("  subirr:      %15ld   %10.2f %%  of subsumed",
      stats.subirr, percent (stats.subirr, stats.subsumed));
    MSG ("  subred:      %15ld   %10.2f %%  of subsumed",
      stats.subred, percent (stats.subred, stats.subsumed));
    MSG ("  subtried:    %15ld   %10.2f    per conflict",
      stats.subtried, relative (stats.subtried, stats.conflicts));
    MSG ("  subchecks:   %15ld   %10.2f    per tried",
      stats.subchecks, relative (stats.subchecks, stats.subtried));
  }
  MSG ("searched:      %15ld   %10.2f    per decision",
    stats.searched, relative (stats.searched, stats.decisions));
  MSG ("bumped:        %15ld   %10.2f    per conflict",
    stats.bumped, relative (stats.bumped, stats.conflicts));
  MSG ("reduced:       %15ld   %10.2f %%  clauses per conflict",
    stats.reduced, percent (stats.reduced, stats.conflicts));
  MSG ("collected:     %15ld   %10.2f    bytes and MB",
    stats.collected, stats.collected/(double)(1l<<20));
  MSG ("maxbytes:      %15ld   %10.2f    bytes and MB",
    m, m/(double)(1l<<20));
  MSG ("time:          %15s   %10.2f    seconds", "", t);
  MSG ("");
}

};
