#ifndef _limit_hpp_INCLUDED
#define _limit_hpp_INCLUDED

namespace CaDiCaL {

struct Limit {

  long conflict;  // conflict limit if non-negative
  long decision;  // decision limit if non-negative

  long elim;      // conflict limit for next 'elim'
  long probe;     // conflict limit for next 'probe'
  long reduce;    // conflict limit for next 'reduce'
  long rephase;   // conflict limit for next 'rephase'
  long restart;   // conflict limit for next 'restart'
  long subsume;   // conflict limit for next 'subsume'
  long compact;   // conflict limit for next 'compact'
  long stabilize; // conflict limit for next 'stabilize'
  long flush;     // conflict limit for next 'flush'

  int keptsize;   // maximum kept size in 'reduce'
  int keptglue;   // maximum kept glue in 'reduce'

  // Used to schedule elimination and subsumption rounds.
  //
  int         fixed_at_last_elim;
  long subsumptions_at_last_elim;
  long      removed_at_last_elim;

  // Used to wait until and right after next 'reduce'.
  //
  long conflicts_at_last_reduce;

  // Wait for 'opts.reducewait' conflicts after 'restart'.
  //
  long conflicts_at_last_restart;

  // Determines whether marking satisfied clauses and removing falsified
  // literals during garbage collection would make sense or is required.
  //
  int fixed_at_last_collect;

  // Search propagation last time the inprocessor was called.
  //
  struct { long transred, probe, vivify; } search_propagations;

  Limit ();
};

struct Inc {
  long reduce;    // reduce interval increment
  long redinc;    // reduce increment increment
  long subsume;   // subsumption interval increment
  long compact;   // compact interval increment
  long elim;      // elimination interval increment
  long probe;     // failed literal probing interval increment
  long rephase;   // rephasing interval increment (rephase=2)
  long flush;     // flushing learned clauses interval
  Inc ();
};

};

#endif
