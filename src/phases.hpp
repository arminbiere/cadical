#ifndef _phases_hpp_INCLUDED
#define _phases_hpp_INCLUDED

namespace CaDiCaL {

typedef signed char Phase;

struct Phases {

  Phase * saved;        // The actual saved phase.
  Phase * target;       // The current target phase.
  Phase * best;         // The current largest trail phase.
  Phase * prev;         // Previous during local search.
  Phase * min;          // The current minimum unsatisfied phase.

  Phases () : saved (0), target (0), best (0), prev (0), min (0) { }
};

}

#endif
