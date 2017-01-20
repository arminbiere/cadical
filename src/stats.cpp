#include "internal.hpp"

#include <cstring>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

Stats::Stats () { memset (this, 0, sizeof *this); }

/*------------------------------------------------------------------------*/

void Stats::print (Internal * internal) {
#ifndef QUIET
  Stats & stats = internal->stats;
  double t = process_time ();
  size_t m = maximum_resident_set_size ();
  int max_var = internal->external->max_var;
#ifdef STATS
  int verbose = 1;
#else
  int verbose = internal->opts.verbose;
#ifdef LOGGING
  if (internal->opts.log) verbose = 1;
#endif // ifdef LOGGING
#endif // ifdef STATS
  if (internal->opts.profile) internal->print_profile (t);
  SECTION ("statistics");
  MSG ("probings:        %15ld   %10.2f    conflicts per probing",
    stats.probings, relative (stats.conflicts, stats.probings));
  MSG ("vivifications:   %15ld   %10.2f    conflicts per vivification",
    stats.vivifications, relative (stats.conflicts, stats.vivifications));
  MSG ("transreductions: %15ld   %10.2f    conflicts per reduction",
    stats.transreds, relative (stats.conflicts, stats.transreds));
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
  MSG ("compacts:        %15ld   %10.2f    conflicts per compact",
    stats.compacts, relative (stats.conflicts, stats.compacts));
  MSG ("conflicts:       %15ld   %10.2f    per second",
    stats.conflicts, relative (stats.conflicts, t));
  MSG ("decisions:       %15ld   %10.2f    per second",
    stats.decisions, relative (stats.decisions, t));
  long propagations = stats.propagations.search;
  propagations += stats.propagations.transred;
  propagations += stats.propagations.probe;
  propagations += stats.propagations.vivify;
  MSG ("propagations:    %15ld   %10.2f    millions per second",
    propagations, relative (propagations/1e6, t));
  if (verbose) 
  {
  MSG ("  searchprops:   %15ld   %10.2f %%  of propagations",
    stats.propagations.search,
    percent (stats.propagations.search, propagations));
  MSG ("  transredprops: %15ld   %10.2f %%  of propagations",
    stats.propagations.transred,
    percent (stats.propagations.transred, propagations));
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
  if (verbose) {
  MSG ("  vivifychecks:  %15ld   %10.2f %%  per conflict",
    stats.vivifychecks, percent (stats.vivifychecks, stats.conflicts));
  MSG ("  vivifysched:   %15ld   %10.2f %%  checks per scheduled",
    stats.vivifysched, percent (stats.vivifychecks, stats.vivifysched));
  MSG ("  vivifyunits:   %15ld   %10.2f %%  per vivify check",
    stats.vivifyunits,
    percent (stats.vivifyunits, stats.vivifychecks));
  MSG ("  vivifysubs:    %15ld   %10.2f %%  per subsumed",
    stats.vivifysubs, percent (stats.vivifysubs, stats.subsumed));
  MSG ("  vivifystrs:    %15ld   %10.2f %%  per strengthened",
    stats.vivifystrs, percent (stats.vivifystrs, stats.strengthened));
  MSG ("  vivifydecs:    %15ld   %10.2f    per checks",
    stats.vivifydecs, relative (stats.vivifydecs, stats.vivifychecks));
  MSG ("  vivifyreused:  %15ld   %10.2f %%  per decision",
    stats.vivifyreused, percent (stats.vivifyreused, stats.vivifydecs));
  }
  MSG ("reused:          %15ld   %10.2f %%  per restart",
    stats.reused, percent (stats.reused, stats.restarts));
  MSG ("resolutions:     %15ld   %10.2f    per eliminated",
    stats.elimres, relative (stats.elimres, stats.all.eliminated));
  if (verbose) {
  MSG ("  elimres2:      %15ld   %10.2f %%  per resolved",
    stats.elimres2, percent (stats.elimres, stats.elimres));
  MSG ("  elimrestried:  %15ld   %10.2f %%  per resolved",
    stats.elimrestried, percent (stats.elimrestried, stats.elimres));
  }
  MSG ("eliminated:      %15ld   %10.2f %%  of all variables",
    stats.all.eliminated, percent (stats.all.eliminated, max_var));
  MSG ("fixed:           %15ld   %10.2f %%  of all variables",
    stats.all.fixed, percent (stats.all.fixed, max_var));
  if (verbose) {
  MSG ("  units:         %15ld   %10.2f    conflicts per unit",
    stats.units, relative (stats.conflicts, stats.units));
  MSG ("  binaries:      %15ld   %10.2f    conflicts per binary",
    stats.binaries, relative (stats.conflicts, stats.binaries));
  }
  MSG ("substituted:     %15ld   %10.2f %%  of all variables",
    stats.all.substituted, percent (stats.all.substituted, max_var));
  MSG ("failed:          %15ld   %10.2f %%  of all variables",
    stats.failed, percent (stats.failed, max_var));
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
  if (verbose) {
  MSG ("  duplicated:    %15ld   %10.2f %%  per subsumed",
    stats.duplicated, percent (stats.duplicated, stats.subsumed));
  MSG ("  transitive:    %15ld   %10.2f %%  per subsumed",
    stats.transitive, percent (stats.transitive, stats.subsumed));
  }
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
  size_t extendbytes = internal->external->extension.capacity ();
  extendbytes *= sizeof (int);
  // if (verbose)
  MSG ("  extendbytes:   %15ld   %10.2f    bytes and MB",
    extendbytes,
    extendbytes/(double)(1l<<20));
  MSG ("memory:          %15ld   %10.2f    bytes and MB",
    m, m/(double)(1l<<20));
  MSG ("time:            %15s   %10.2f    seconds", "", t);
  MSG ("");
#endif
}

};
