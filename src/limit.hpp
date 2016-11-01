#ifndef _limit_hpp_INCLUDED
#define _limit_hpp_INCLUDED

namespace CaDiCaL {

struct Limit {

  long reduce;    // conflict limit for next 'reduce'
  long resolved;  // limit on keeping recently resolved clauses
  long restart;   // conflict limit for next 'restart'
  long subsume;   // conflict limit on next 'subsume'
  long elim;      // conflict limit on next 'eliminate'

  long conflict;  // conflict limit if non-negative
  long decision;  // decision limit if non-negative

  int keptglue;   // maximum kept glue in 'reduce'
  int keptsize;   // maximum kept size in 'reduce'

  int decision_level_at_last_restart;
  long conflicts_at_last_restart;

  int fixed_at_last_elim;
  long irredundant_at_last_elim;

  long conflicts_at_last_reduce;
  int fixed_at_last_collect;

  Limit ();
};

};

#endif
