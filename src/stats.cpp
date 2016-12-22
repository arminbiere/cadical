#include "internal.hpp"

#include "macros.hpp"
#include "message.hpp"
#include "util.hpp"

#include <cstring>
#include <cstdio>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

Stats::Stats () { memset (this, 0, sizeof *this); }

/*------------------------------------------------------------------------*/

void Stats::print (Internal * internal) {
  Stats & stats = internal->stats;
  double t = process_time ();
  size_t m = maximum_resident_set_size ();
#ifdef STATS
  int verbose = 1;
#else
  int verbose = internal->opts.verbose;
#ifdef LOGGING
  if (internal->opts.log) verbose = 1;
#endif
#endif//outer
  if (internal->opts.profile) internal->print_profile (t);
  SECTION ("statistics");
  MSG ("probings:        %15ld   %10.2f    conflicts per probing",
    stats.probings, relative (stats.conflicts, stats.probings));
  MSG ("vivifications:   %15ld   %10.2f    conflicts per vivification",
    stats.vivifications, relative (stats.conflicts, stats.vivifications));
  MSG ("eliminations:    %15ld   %10.2f    conflicts per elimination",
    stats.eliminations, relative (stats.conflicts, stats.eliminations));
  MSG ("subsumptions:    %15ld   %10.2f    conflicts per subsumption",
    stats.subsumptions, relative (stats.conflicts, stats.subsumptions));
  MSG ("decompositions:  %15ld   %10.2f    decompositions per probing",
    stats.decompositions,
    relative (stats.decompositions, stats.probings));
  MSG ("reductions:      %15ld   %10.2f    conflicts per reduction",
    stats.reductions, relative (stats.conflicts, stats.reductions));
  MSG ("restarts:        %15ld   %10.2f    conflicts per restart",
    stats.restarts, relative (stats.conflicts, stats.restarts));
  MSG ("conflicts:       %15ld   %10.2f    per second",
    stats.conflicts, relative (stats.conflicts, t));
  MSG ("decisions:       %15ld   %10.2f    per second",
    stats.decisions, relative (stats.decisions, t));
  long propagations = stats.propagations.probe;
  propagations += stats.propagations.search;
  propagations += stats.propagations.vivify;
  MSG ("propagations:    %15ld   %10.2f    millions per second",
    propagations, relative (propagations/1e6, t));
  if (verbose) {
  MSG ("  searchprops:   %15ld   %10.2f %%  of propagations",
    stats.propagations.search,
    percent (stats.propagations.search, propagations));
  MSG ("  probeprops:    %15ld   %10.2f %%  of propagations",
    stats.propagations.probe,
    percent (stats.propagations.probe, propagations));
  MSG ("  vivifyprops:   %15ld   %10.2f %%  of propagations",
    stats.propagations.vivify,
    percent (stats.propagations.vivify, propagations));
#ifdef STATS
  MSG ("  visits:        %15ld   %10.2f    per searchprop",
    stats.visits, relative (stats.visits, stats.propagations.search));
  MSG ("  traversed:     %15ld   %10.2f    per visit",
    stats.traversed, relative (stats.traversed, stats.visits));
#endif
  }
  MSG ("probed:          %15ld   %10.2f    per failed",
    stats.probed, relative (stats.probed, stats.failed));
  if (verbose)
  {
  MSG ("  hbrs:          %15ld   %10.2f    per probed",
    stats.hbrs, relative (stats.hbrs, stats.probed));
  MSG ("  hbrsizes:      %15ld   %10.2f    per hbr",
    stats.hbrsizes, relative (stats.hbrsizes, stats.hbrs));
  MSG ("  hbreds:        %15ld   %10.2f %%  per hbr",
    stats.hbreds, percent (stats.hbreds, stats.hbrs));
  MSG ("  hbrsubs:       %15ld   %10.2f %%  per hbr",
    stats.hbrsubs, percent (stats.hbrsubs, stats.hbrs));
  }
  long vivified = stats.vivifysubs + stats.vivifystrs;
  MSG ("vivified:        %15ld   %10.2f %%  per vivify check",
    vivified, percent (vivified, stats.vivifychecks));
  //if (verbose) {
  MSG ("  vivifychecks:  %15ld   %10.2f %%  per conflict",
    stats.vivifychecks, percent (stats.vivifychecks, stats.conflicts));
  MSG ("  vivifyunits:   %15ld   %10.2f %%  per vivify check",
    stats.vivifyunits,
    percent (stats.vivifyunits, stats.vivifychecks));
  MSG ("  vivifysubs:    %15ld   %10.2f %%  per subsumed",
    stats.vivifysubs, percent (stats.vivifysubs, stats.subsumed));
  MSG ("  vivifystrs:    %15ld   %10.2f %%  per strengthened",
    stats.vivifystrs, percent (stats.vivifystrs, stats.strengthened));
  //}
  MSG ("reused:          %15ld   %10.2f %%  per restart",
    stats.reused, percent (stats.reused, stats.restarts));
  MSG ("resolutions:     %15ld   %10.2f    per eliminated",
    stats.elimres, relative (stats.elimres, stats.eliminated));
  if (verbose) {
  MSG ("  elimres2:      %15ld   %10.2f %%  per resolved",
    stats.elimres2, percent (stats.elimres, stats.elimres));
  MSG ("  elimrestried:  %15ld   %10.2f %%  per resolved",
    stats.elimrestried, percent (stats.elimrestried, stats.elimres));
  }
  MSG ("eliminated:      %15ld   %10.2f %%  of all variables",
    stats.eliminated, percent (stats.eliminated, internal->max_var));
  MSG ("fixed:           %15ld   %10.2f %%  of all variables",
    stats.fixed, percent (stats.fixed, internal->max_var));
  if (verbose) {
  MSG ("  units:         %15ld   %10.2f    conflicts per unit",
    stats.units, relative (stats.conflicts, stats.units));
  MSG ("  binaries:      %15ld   %10.2f    conflicts per binary",
    stats.binaries, relative (stats.conflicts, stats.binaries));
  }
  MSG ("substituted:     %15ld   %10.2f %%  of all variables",
    stats.substituted, percent (stats.substituted, internal->max_var));
  MSG ("failed:          %15ld   %10.2f %%  of all variables",
    stats.failed, percent (stats.failed, internal->max_var));
  long learned = stats.learned - stats.minimized;
  MSG ("learned:         %15ld   %10.2f    per conflict",
    learned, relative (learned, stats.conflicts));
  if (verbose) {
  MSG ("  analyzed:      %15ld   %10.2f    per conflict",
    stats.analyzed, relative (stats.analyzed, stats.conflicts));
  MSG ("  trailbumped:   %15ld   %10.2f %%  per conflict",
    stats.trailbumped, percent (stats.trailbumped, stats.conflicts));
  }
  MSG ("minimized:       %15ld   %10.2f %%  of 1st-UIP-literals",
    stats.minimized, percent (stats.minimized, stats.learned));
  MSG ("subsumed:        %15ld   %10.2f    tried per subsumed",
    stats.subsumed, relative (stats.subtried, stats.subsumed));
  if (verbose)
  MSG ("  duplicated:    %15ld   %10.2f %%  per subsumed",
    stats.duplicated, percent (stats.duplicated, stats.subsumed));
  MSG ("strengthened:    %15ld   %10.2f    per subsumed",
    stats.strengthened, relative (stats.strengthened, stats.subsumed));
  if (verbose) {
  MSG ("  subirr:        %15ld   %10.2f %%  of subsumed",
    stats.subirr, percent (stats.subirr, stats.subsumed));
  MSG ("  subred:        %15ld   %10.2f %%  of subsumed",
    stats.subred, percent (stats.subred, stats.subsumed));
  MSG ("  subtried:      %15ld   %10.2f    per conflict",
    stats.subtried, relative (stats.subtried, stats.conflicts));
  MSG ("  subchecks:     %15ld   %10.2f    per tried",
    stats.subchecks, relative (stats.subchecks, stats.subtried));
  MSG ("  subchecks2:    %15ld   %10.2f %%  per subcheck",
    stats.subchecks2, percent (stats.subchecks2, stats.subchecks));
  }
  MSG ("searched:        %15ld   %10.2f    per decision",
    stats.searched, relative (stats.searched, stats.decisions));
  MSG ("bumped:          %15ld   %10.2f    per conflict",
    stats.bumped, relative (stats.bumped, stats.conflicts));
  MSG ("reduced:         %15ld   %10.2f %%  clauses per conflict",
    stats.reduced, percent (stats.reduced, stats.conflicts));
  if (verbose)
  MSG ("  collections:   %15ld   %10.2f    conflicts per collection",
    stats.collections, relative (stats.conflicts, stats.collections));
  MSG ("collected:       %15ld   %10.2f    bytes and MB",
    stats.collected, stats.collected/(double)(1l<<20));
  MSG ("memory:          %15ld   %10.2f    bytes and MB",
    m, m/(double)(1l<<20));
  MSG ("time:            %15s   %10.2f    seconds", "", t);
  MSG ("");
}

};
