// vim: set tw=300: set VIM text width to 300 characters for this file.

#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

Stats::Stats () {
  time.real = absolute_real_time ();
  time.process = absolute_process_time ();
  walk_minimum = INT64_MAX;
  used[0].resize (127);
  used[1].resize (127);
}

/*------------------------------------------------------------------------*/

#define PRT(FMT, ...) \
  do { \
    if (FMT[0] == ' ' && !all) \
      break; \
    MSG (FMT, __VA_ARGS__); \
  } while (0)

/*------------------------------------------------------------------------*/
#ifndef QUIET
// Names are shortened to be 21 chars (22 with ':')
// absolute numbers may be higher then 15 (should be rare though)
// REF_OFFSET is 12 for old stat format but that spills over
// PREFIX, NAME, SPACE, NUM, SPACE, REF, SPACE, SYMBOL, SPACE, PRINT
// 2 + 22 + 1 + 15 + 1 + 11 + 1 + 3 + 1 + 21 = 80
#define NAME_OFFSET "22"
#define NUM_OFFSET "15"
#define REF_OFFSET "11.2"
#define SYMBOL_OFFSET "3"
#define PRINT_OFFSET "21"

#define RELPROFW(FIRST, IGNORE) \
  relative (1e-6 * FIRST, internal->profiles.walk.value)
#define SECONDS(FIRST, IGNORE) relative (FIRST, t)
#define MSECONDS(FIRST, IGNORE) relative (1e-6 * FIRST, t)
#define INTERVAL(FIRST, IGNORE) relative (conflicts, FIRST)
#define NOTHING(FIRST, IGNORE) 0

#define PRINT_STATER(NAME, NUM, VERBOSE, OTHER_NUM, SYMBOL, PRINT) \
  do { \
    if (VERBOSE > verbose) \
      break; \
    if (!NUM && VERBOSE == verbose) \
      break; \
    const double RELATIVE = OTHER_NUM; \
    const char *SAVED_SYMBOL = (const char *) (SYMBOL); \
    const char *SAVED_PRINT = (const char *) (PRINT); \
    if (SYMBOL == 0) \
      MSG ("%-" NAME_OFFSET "s %" NUM_OFFSET PRId64, NAME ":", NUM); \
    else \
      MSG ("%-" NAME_OFFSET "s %" NUM_OFFSET PRId64 " %" REF_OFFSET \
           "f %-" SYMBOL_OFFSET "s %-" PRINT_OFFSET "s", \
           NAME ":", NUM, RELATIVE, SAVED_SYMBOL, SAVED_PRINT); \
  } while (0)

void Stats::print_internal_stats (Internal *internal) {

  Stats stats = internal->stats;
  int verbose = internal->opts.verbose;
  verbose += internal->opts.stats;

#ifdef LOGGING
  if (internal->opts.log)
    verbose = 4;
#endif // ifdef LOGGING

  double t = internal->solve_time ();

#define STATISTIC(NAME, VERBOSE, COMMAND, SYMBOL, OTHER) \
  PRINT_STATER (#NAME, (int64_t) stats.NAME, VERBOSE, \
                COMMAND (NAME, OTHER), SYMBOL, #OTHER);
#ifndef NMETRICS
#define METRIC(NAME, VERBOSE, COMMAND, SYMBOL, OTHER) \
  STATISTIC (NAME, VERBOSE, COMMAND, SYMBOL, OTHER)
#else
#define METRIC(NAME, VERBOSE, COMMAND, SYMBOL, OTHER)
#endif
  CADICAL_STATISTICS

#undef STATISTIC
#undef METRIC
}
#endif

void Stats::print (Internal *internal) {

#ifdef QUIET
  (void) internal;
#else

  if (internal->opts.profile)
    internal->print_profile ();

  int verbosity = internal->opts.verbose + internal->opts.stats;
  if (verbosity < 0)
    return;

  SECTION ("statistics");

  print_internal_stats (internal);

  LINE ();
  MSG ("%sseconds are measured in %s time for solving%s",
       tout.magenta_code (), internal->opts.realtime ? "real" : "process",
       tout.normal_code ());

  if (verbosity <= 0)
    return;

  SECTION ("glue usage");

  internal->print_tier_usage_statistics ();

#endif // ifndef QUIET
}

void Internal::print_resource_usage () {
#ifndef QUIET
  SECTION ("resources");
  uint64_t m = maximum_resident_set_size ();
  MSG ("total process time since initialization: %12.2f    seconds",
       internal->process_time ());
  MSG ("total real time since initialization:    %12.2f    seconds",
       internal->real_time ());
  MSG ("maximum resident set size of process:    %12.2f    MB",
       m / (double) (1l << 20));
#endif
}

/*------------------------------------------------------------------------*/

void Checker::print_stats () {

  if (!stats.added && !stats.deleted)
    return;

  SECTION ("checker statistics");

  MSG ("checks:          %15" PRId64 "", stats.checks);
  MSG ("assumptions:     %15" PRId64 "   %10.2f    per check",
       stats.assumptions, relative (stats.assumptions, stats.checks));
  MSG ("propagations:    %15" PRId64 "   %10.2f    per check",
       stats.propagations, relative (stats.propagations, stats.checks));
  MSG ("original:        %15" PRId64 "   %10.2f %%  of all clauses",
       stats.original, percent (stats.original, stats.added));
  MSG ("derived:         %15" PRId64 "   %10.2f %%  of all clauses",
       stats.derived, percent (stats.derived, stats.added));
  MSG ("deleted:         %15" PRId64 "   %10.2f %%  of all clauses",
       stats.deleted, percent (stats.deleted, stats.added));
  MSG ("insertions:      %15" PRId64 "   %10.2f %%  of all clauses",
       stats.insertions, percent (stats.insertions, stats.added));
  MSG ("collections:     %15" PRId64 "   %10.2f    deleted per collection",
       stats.collections, relative (stats.collections, stats.deleted));
  MSG ("collisions:      %15" PRId64 "   %10.2f    per search",
       stats.collisions, relative (stats.collisions, stats.searches));
  MSG ("searches:        %15" PRId64 "", stats.searches);
  MSG ("units:           %15" PRId64 "", stats.units);
}

void LratChecker::print_stats () {

  if (!stats.added && !stats.deleted)
    return;

  SECTION ("lrat checker statistics");

  MSG ("checks:          %15" PRId64 "", stats.checks);
  MSG ("insertions:      %15" PRId64 "   %10.2f %%  of all clauses",
       stats.insertions, percent (stats.insertions, stats.added));
  MSG ("original:        %15" PRId64 "   %10.2f %%  of all clauses",
       stats.original, percent (stats.original, stats.added));
  MSG ("derived:         %15" PRId64 "   %10.2f %%  of all clauses",
       stats.derived, percent (stats.derived, stats.added));
  MSG ("rat:             %15" PRId64 "   %10.2f %%  of derived clauses",
       stats.rat, percent (stats.rat, stats.derived));
  MSG ("deleted:         %15" PRId64 "   %10.2f %%  of all clauses",
       stats.deleted, percent (stats.deleted, stats.added));
  MSG ("finalized:       %15" PRId64 "   %10.2f %%  of all clauses",
       stats.finalized, percent (stats.finalized, stats.added));
  MSG ("collections:     %15" PRId64 "   %10.2f    deleted per collection",
       stats.collections, relative (stats.collections, stats.deleted));
  MSG ("collisions:      %15" PRId64 "   %10.2f    per search",
       stats.collisions, relative (stats.collisions, stats.searches));
  MSG ("searches:        %15" PRId64 "", stats.searches);
}

} // namespace CaDiCaL
