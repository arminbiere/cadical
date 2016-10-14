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
    stats.reduce.count, relative (stats.conflicts, stats.reduce.count));
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
  MSG ("resolved:      %15ld   %10.2f    per conflict",
    stats.resolved, relative (stats.resolved, stats.conflicts));
  long learned = stats.literals.learned - stats.literals.minimized;
  MSG ("learned:       %15ld   %10.2f    per conflict",
    learned, relative (learned, stats.conflicts));
  MSG ("minimized:     %15ld   %10.2f %%  of 1st-UIP-literals",
    stats.literals.minimized,
    percent (stats.literals.minimized, stats.literals.learned));
  MSG ("searched:      %15ld   %10.2f    per decision",
    stats.searched, relative (stats.searched, stats.decisions));
  MSG ("bumped:        %15ld   %10.2f    per conflict",
    stats.bumped, relative (stats.bumped, stats.conflicts));
  MSG ("collected:     %15ld   %10.2f    clauses and MB",
    stats.reduce.clauses, stats.reduce.bytes/(double)(1l<<20));
  MSG ("maxbytes:      %15ld   %10.2f    MB",
    m, m/(double)(1l<<20));
  MSG ("time:          %15s   %10.2f    seconds", "", t);
  MSG ("");
}

};
