#ifndef _var_hpp_INCLUDED
#define _var_hpp_INCLUDED

namespace CaDiCaL {

class Clause;

// This structure captures data associated with an assigned variable.

struct Var {

  // Note that none of these members is valid unless the variable is
  // assigned.  Thus during unassigning it we do not reset it.

  int level;            // decision level
  int trail;            // trail
  Clause * reason;      // implication graph edge through clause
};

};

#endif
