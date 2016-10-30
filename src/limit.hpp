#ifndef _limit_hpp_INCLUDED
#define _limit_hpp_INCLUDED

namespace CaDiCaL {

struct Limit {

  long reduce;    // conflict limit for next 'reduce'
  long resolved;  // limit on keeping recently resolved clauses
  long restart;   // conflict limit for next 'restart'
  long subsume;   // next subsumption check

  long conflict;  // conflict limit if non-negative
  long decision;  // decision limit if non-negative

  int fixed;      // number of units in 'collect'
  int keptglue;   // maximum kept glue in 'reduce'
  int keptsize;   // maximum kept size in 'reduce'

  long conflicts_at_last_reduce;
  long conflicts_at_last_restart;
  int decision_level_at_last_restart;
  long propagations_at_last_conflict;

  Limit ();
};

};

#endif
