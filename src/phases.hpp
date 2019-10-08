#ifndef _phases_hpp_INCLUDED
#define _phases_hpp_INCLUDED

namespace CaDiCaL {

struct Phases {

  vector<signed char> saved;   // The actual saved phase.
  vector<signed char> target;  // The current target phase.
  vector<signed char> best;    // The current largest trail phase.
  vector<signed char> prev;    // Previous during local search.
  vector<signed char> min;     // The current minimum unsatisfied phase.

};

}

#endif
