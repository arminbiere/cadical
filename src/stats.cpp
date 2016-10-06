#include "cadical.hpp"

#include <cstring>
#include <cstdio>

namespace CaDiCaL {

Stats::Stats (Solver * s) {
  memset (this, 0, sizeof *this);
  solver = s;
}

void Stats::print () {
  Stats & stats = solver->stats;
  double t = solver->seconds ();
#ifdef PROFILING
  solver->print_profile (t);
#endif
  size_t m = solver->max_bytes ();
  SECTION ("statistics");
  MSG ("conflicts:     %15ld   %10.2f    per second",
    stats.conflicts, relative (stats.conflicts, t));
  MSG ("decisions:     %15ld   %10.2f    per second",
    stats.decisions, relative (stats.decisions, t));
  MSG ("propagations:  %15ld   %10.2f    millions per second",
    stats.propagations, relative (stats.propagations/1e6, t));
  MSG ("reductions:    %15ld   %10.2f    conflicts per reduction",
    stats.reduce.count, relative (stats.conflicts, stats.reduce.count));
  MSG ("restarts:      %15ld   %10.2f    conflicts per restart",
    stats.restart.count, relative (stats.conflicts, stats.restart.count));
  MSG ("tried:         %15ld   %10.2f    per restart",
    stats.restart.tried,
    relative (stats.restart.tried, stats.restart.count));
  MSG ("reused:        %15ld   %10.2f %%  per restart",
    stats.restart.reused,
    percent (stats.restart.reused, stats.restart.count));
  MSG ("blocked:       %15ld   %10.2f %%  per restart",
    stats.restart.blocked,
    percent (stats.restart.blocked, stats.restart.count));
  MSG ("unforced:      %15ld   %10.2f %%  per restart",
    stats.restart.unforced,
    percent (stats.restart.unforced, stats.restart.count));
  MSG ("forced:        %15ld   %10.2f %%  per restart",
    stats.restart.forced,
    percent (stats.restart.forced, stats.restart.count));
  MSG ("f1restart:     %15ld   %10.2f %%  per restart",
    stats.restart.unit,
    percent (stats.restart.unit, stats.restart.count));
  MSG ("units:         %15ld   %10.2f    conflicts per unit",
    stats.learned.unit, relative (stats.conflicts, stats.learned.unit));
  MSG ("binaries:      %15ld   %10.2f    conflicts per binary",
    stats.learned.binary, relative (stats.conflicts, stats.learned.binary));
  MSG ("bumped:        %15ld   %10.2f    per conflict",
    stats.bumped, relative (stats.bumped, stats.conflicts));
  MSG ("resolved:      %15ld   %10.2f    per conflict",
    stats.resolved, relative (stats.resolved, stats.conflicts));
  MSG ("searched:      %15ld   %10.2f    per decision",
    stats.searched, relative (stats.searched, stats.decisions));
  long learned = stats.literals.learned - stats.literals.minimized;
  MSG ("learned:       %15ld   %10.2f    per conflict",
    learned, relative (learned, stats.conflicts));
  MSG ("minimized:     %15ld   %10.2f %%  of 1st-UIP-literals",
    stats.literals.minimized,
    percent (stats.literals.minimized, stats.literals.learned));
  MSG ("collected:     %15ld   %10.2f    clauses and MB",
    stats.reduce.clauses, stats.reduce.bytes/(double)(1l<<20));
  MSG ("maxbytes:      %15ld   %10.2f    MB",
    m, m/(double)(1l<<20));
  MSG ("time:          %15s   %10.2f    seconds", "", t);
  MSG ("");
}

};
