#ifndef _limit_hpp_INCLUDED
#define _limit_hpp_INCLUDED

namespace CaDiCaL {

struct Limit {

  long conflict;  // conflict limit if non-negative
  long decision;  // decision limit if non-negative

  long elim;      // conflict limit for next 'elim'
  long probe;     // conflict limit for next 'probe'
  long reduce;    // conflict limit for next 'reduce'
  long restart;   // conflict limit for next 'restart'
  long subsume;   // conflict limit for next 'subsume'

  long analyzed;  // limit on keeping recently analyzed clauses

  int keptglue;   // maximum kept glue in 'reduce'
  int keptsize;   // maximum kept size in 'reduce'

  // Used to schedule elimination and subsumption rounds.
  //
  int         fixed_at_last_elim;
  long subsumptions_at_last_elim;
  long      removed_at_last_elim;

  // Used to let 'subsume' wait until and right after next 'reduce'.
  //
  long conflicts_at_last_reduce;

  // Determines whether marking satisfied clauses and removing falsified
  // literals during garbage collection would make sense or is required.
  //
  int fixed_at_last_collect;

  // Used by persistent 'VarIdxIterator' of 'probe'.
  //
  int last_probed;

  Limit ();
};

};

#endif
