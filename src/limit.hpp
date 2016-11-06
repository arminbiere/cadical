#ifndef _limit_hpp_INCLUDED
#define _limit_hpp_INCLUDED

namespace CaDiCaL {

struct Limit {

  long reduce;    // conflict limit for next 'reduce'
  long analyzed;  // limit on keeping recently analyzed clauses
  long restart;   // conflict limit for next 'restart'
  long subsume;   // conflict limit on next 'subsume'
  long elim;      // conflict limit on next 'eliminate'

  long conflict;  // conflict limit if non-negative
  long decision;  // decision limit if non-negative

  int keptglue;   // maximum kept glue in 'reduce'
  int keptsize;   // maximum kept size in 'reduce'

  // Used to compute restart efficiency and interval.
  //
  int decision_level_at_last_restart;
  long     conflicts_at_last_restart;

  // Used to prohibit useless elimination attempts.
  //
  int         fixed_at_last_elim;
  long  irredundant_at_last_elim;
  long subsumptions_at_last_elim;

  // Used to let 'subsume' wait until and right after next 'reduce'.
  //
  long conflicts_at_last_reduce;

  // Determines whether marking satisfied clauses and removing falsified
  // literals during garbage collection would make sense or is required.
  //
  int fixed_at_last_collect;

  Limit ();
};

};

#endif
