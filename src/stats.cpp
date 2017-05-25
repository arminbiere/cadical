#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

Stats::Stats () { memset (this, 0, sizeof *this); }

/*------------------------------------------------------------------------*/

#define PRT(FMT,ARGS...) \
do { \
  if (FMT[0] == ' ' && !verbose) break; \
  MSG (FMT, ##ARGS); \
} while (0)

#ifdef STATS
#define SSG PRT
#else
#define SSG(ARGS...) do { } while (0)
#endif

/*------------------------------------------------------------------------*/

void Stats::print (Internal * internal) {

#ifndef QUIET

#ifdef STATS
  int verbose = 1;
#else
  int verbose = internal->opts.verbose;
#ifdef LOGGING
  if (internal->opts.log) verbose = 1;
#endif // ifdef LOGGING
#endif // ifdef STATS

  double t = process_time ();
  if (internal->opts.profile) internal->print_profile (t);
  Stats & stats = internal->stats;
  size_t m = maximum_resident_set_size ();
  int max_var = internal->external->max_var;
  long propagations = stats.propagations.search;
  propagations += stats.propagations.transred;
  propagations += stats.propagations.probe;
  propagations += stats.propagations.vivify;
  long vivified = stats.vivifysubs + stats.vivifystrs;
  long learned = stats.learned - stats.minimized;
  size_t extendbytes = internal->external->extension.capacity ();
  extendbytes *= sizeof (int);

  SECTION ("statistics");

  PRT ("bumped:          %15ld   %10.2f    per conflict", stats.bumped, relative (stats.bumped, stats.conflicts));
  PRT ("compacts:        %15ld   %10.2f    conflicts per compact", stats.compacts, relative (stats.conflicts, stats.compacts));
  PRT ("conflicts:       %15ld   %10.2f    per second", stats.conflicts, relative (stats.conflicts, t));
  PRT ("decisions:       %15ld   %10.2f    per second", stats.decisions, relative (stats.decisions, t));
  PRT ("decompositions:  %15ld   %10.2f    decompositions per probing", stats.decompositions, relative (stats.decompositions, stats.probings));
  PRT ("eliminated:      %15ld   %10.2f %%  of all variables", stats.all.eliminated, percent (stats.all.eliminated, max_var));
  PRT ("eliminations:    %15ld   %10.2f    conflicts per elimination", stats.eliminations, relative (stats.conflicts, stats.eliminations));
  PRT ("failed:          %15ld   %10.2f %%  of all variables", stats.failed, percent (stats.failed, max_var));
  PRT ("fixed:           %15ld   %10.2f %%  of all variables", stats.all.fixed, percent (stats.all.fixed, max_var));
  PRT ("  units:         %15ld   %10.2f    conflicts per unit", stats.units, relative (stats.conflicts, stats.units));
  PRT ("  binaries:      %15ld   %10.2f    conflicts per binary", stats.binaries, relative (stats.conflicts, stats.binaries));
  PRT ("learned:         %15ld   %10.2f    per conflict", learned, relative (learned, stats.conflicts));
  PRT ("memory:          %15ld   %10.2f    bytes and MB", m, m/(double)(1l<<20));
  PRT ("minimized:       %15ld   %10.2f %%  of 1st-UIP-literals", stats.minimized, percent (stats.minimized, stats.learned));
  PRT ("probings:        %15ld   %10.2f    conflicts per probing", stats.probings, relative (stats.conflicts, stats.probings));
  PRT ("probed:          %15ld   %10.2f    per failed", stats.probed, relative (stats.probed, stats.failed));
  PRT ("  hbrs:          %15ld   %10.2f    per probed", stats.hbrs, relative (stats.hbrs, stats.probed));
  PRT ("  hbrsizes:      %15ld   %10.2f    per hbr", stats.hbrsizes, relative (stats.hbrsizes, stats.hbrs));
  PRT ("  hbreds:        %15ld   %10.2f %%  per hbr", stats.hbreds, percent (stats.hbreds, stats.hbrs));
  PRT ("  hbrsubs:       %15ld   %10.2f %%  per hbr", stats.hbrsubs, percent (stats.hbrsubs, stats.hbrs));
  PRT ("propagations:    %15ld   %10.2f    millions per second", propagations, relative (propagations/1e6, t));
  PRT ("  searchprops:   %15ld   %10.2f %%  of propagations", stats.propagations.search, percent (stats.propagations.search, propagations));
  PRT ("  transredprops: %15ld   %10.2f %%  of propagations", stats.propagations.transred, percent (stats.propagations.transred, propagations));
  PRT ("  probeprops:    %15ld   %10.2f %%  of propagations", stats.propagations.probe, percent (stats.propagations.probe, propagations));
  PRT ("  vivifyprops:   %15ld   %10.2f %%  of propagations", stats.propagations.vivify, percent (stats.propagations.vivify, propagations));
  SSG ("  visits:        %15ld   %10.2f    per searchprop", stats.visits, relative (stats.visits, stats.propagations.search));
  SSG ("  traversed:     %15ld   %10.2f    per visit", stats.traversed, relative (stats.traversed, stats.visits));
  PRT ("reduced:         %15ld   %10.2f %%  clauses per conflict", stats.reduced, percent (stats.reduced, stats.conflicts));
  PRT ("  collections:   %15ld   %10.2f    conflicts per collection", stats.collections, relative (stats.conflicts, stats.collections));
  PRT ("  extendbytes:   %15ld   %10.2f    bytes and MB", extendbytes, extendbytes/(double)(1l<<20));
  PRT ("reductions:      %15ld   %10.2f    conflicts per reduction", stats.reductions, relative (stats.conflicts, stats.reductions));
  PRT ("rephased:        %15ld   %10.2f    conflicts per rephase", stats.rephased, relative (stats.conflicts, stats.rephased));
  PRT ("resolutions:     %15ld   %10.2f    per eliminated", stats.elimres, relative (stats.elimres, stats.all.eliminated));
  PRT ("  elimres2:      %15ld   %10.2f %%  per resolved", stats.elimres2, percent (stats.elimres, stats.elimres));
  PRT ("  elimrestried:  %15ld   %10.2f %%  per resolved", stats.elimrestried, percent (stats.elimrestried, stats.elimres));
  PRT ("restarts:        %15ld   %10.2f    conflicts per restart", stats.restarts, relative (stats.conflicts, stats.restarts));
  PRT ("reused:          %15ld   %10.2f %%  per restart", stats.reused, percent (stats.reused, stats.restarts));
  PRT ("searched:        %15ld   %10.2f    per decision", stats.searched, relative (stats.searched, stats.decisions));
  PRT ("strengthened:    %15ld   %10.2f    per subsumed", stats.strengthened, relative (stats.strengthened, stats.subsumed));
  PRT ("  subirr:        %15ld   %10.2f %%  of subsumed", stats.subirr, percent (stats.subirr, stats.subsumed));
  PRT ("  subred:        %15ld   %10.2f %%  of subsumed", stats.subred, percent (stats.subred, stats.subsumed));
  PRT ("  subtried:      %15ld   %10.2f    per conflict", stats.subtried, relative (stats.subtried, stats.conflicts));
  PRT ("  subchecks:     %15ld   %10.2f    per tried", stats.subchecks, relative (stats.subchecks, stats.subtried));
  PRT ("  subchecks2:    %15ld   %10.2f %%  per subcheck", stats.subchecks2, percent (stats.subchecks2, stats.subchecks));
  PRT ("substituted:     %15ld   %10.2f %%  of all variables", stats.all.substituted, percent (stats.all.substituted, max_var));
  PRT ("subsumed:        %15ld   %10.2f    tried per subsumed", stats.subsumed, relative (stats.subtried, stats.subsumed));
  PRT ("  duplicated:    %15ld   %10.2f %%  per subsumed", stats.duplicated, percent (stats.duplicated, stats.subsumed));
  PRT ("  transitive:    %15ld   %10.2f %%  per subsumed", stats.transitive, percent (stats.transitive, stats.subsumed));
  PRT ("subsumptions:    %15ld   %10.2f    conflicts per subsumption", stats.subsumptions, relative (stats.conflicts, stats.subsumptions));
  PRT ("time:            %15s   %10.2f    seconds", "", t);
  PRT ("transreductions: %15ld   %10.2f    conflicts per reduction", stats.transreds, relative (stats.conflicts, stats.transreds));
  PRT ("vivifications:   %15ld   %10.2f    conflicts per vivification", stats.vivifications, relative (stats.conflicts, stats.vivifications));
  PRT ("vivified:        %15ld   %10.2f %%  per vivify check", vivified, percent (vivified, stats.vivifychecks));
  PRT ("  vivifychecks:  %15ld   %10.2f %%  per conflict", stats.vivifychecks, percent (stats.vivifychecks, stats.conflicts));
  PRT ("  vivifysched:   %15ld   %10.2f %%  checks per scheduled", stats.vivifysched, percent (stats.vivifychecks, stats.vivifysched));
  PRT ("  vivifyunits:   %15ld   %10.2f %%  per vivify check", stats.vivifyunits, percent (stats.vivifyunits, stats.vivifychecks));
  PRT ("  vivifysubs:    %15ld   %10.2f %%  per subsumed", stats.vivifysubs, percent (stats.vivifysubs, stats.subsumed));
  PRT ("  vivifystrs:    %15ld   %10.2f %%  per strengthened", stats.vivifystrs, percent (stats.vivifystrs, stats.strengthened));
  PRT ("  vivifydecs:    %15ld   %10.2f    per checks", stats.vivifydecs, relative (stats.vivifydecs, stats.vivifychecks));
  PRT ("  vivifyreused:  %15ld   %10.2f %%  per decision", stats.vivifyreused, percent (stats.vivifyreused, stats.vivifydecs));

  PRT ("");

#endif // ifndef QUIET

}

};
