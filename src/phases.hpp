#ifndef _phases_hpp_INCLUDED
#define _phases_hpp_INCLUDED

namespace CaDiCaL {

typedef signed char Phase;

struct Phases {

  vector<Phase> saved;   // The actual saved phase.
  vector<Phase> target;  // The current target phase.
  vector<Phase> best;    // The current largest trail phase.
  vector<Phase> prev;    // Previous during local search.
  vector<Phase> min;     // The current minimum unsatisfied phase.

};

}

#endif
