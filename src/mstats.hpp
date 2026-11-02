#ifndef _mstats_h_INCLUDED
#define _mstats_h_INCLUDED

// clang-format off

#define COUNTERS_AND_STATISTICS \
\
  STATISTIC (allocated_current, 2, PCNT_RESIDENT_SET, "%", "resident set") \
  STATISTIC (clause_restored, 1, PER_SEARCH, "", "per solved") \
  STATISTIC (citten_flip, 1, NO_SECONDARY, 0, 0)

// clang-format on

#endif
