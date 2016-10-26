#ifndef _limit_hpp_INCLUDED
#define _limit_hpp_INCLUDED

namespace CaDiCaL {

struct Limit {

  long reduce;    // conflict limit for next 'reduce'
  long resolved;  // limit on keeping recently resolved clauses
  long restart;   // conflict limit for next 'restart'
  long subsume;   // next subsumption check

  long redlast;   // last reduced at this conflict

  int fixed;      // number of units in 'collect'
  int keptglue;   // maximum kept glue in 'reduce'
  int keptsize;   // maximum kept size in 'reduce'

  int lastlevel;  // level at last restart

  Limit () : 
    reduce (0), resolved (0), restart (0), subsume (0),
    redlast (0),
    fixed (0), keptglue (0), keptsize (0)
  { }
};

};

#endif
