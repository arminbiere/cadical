#ifndef _limit_hpp_INCLUDED
#define _limit_hpp_INCLUDED

namespace CaDiCaL {

struct Limit {
  long fixed;     // number of units in 'collect'
  long reduce;    // conflict limit for next 'reduce'
  long resolved;  // limit on keeping recently resolved clauses
  long restart;   // conflict limit for next 'restart'
  long subsume;   // next subsumption check

  Limit () : 
    fixed (0), reduce (0), resolved (0), restart (0), subsume (0)
  { }
};

};

#endif
