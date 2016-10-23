#ifndef _var_hpp_INCLUDED
#define _var_hpp_INCLUDED

namespace CaDiCaL {

class Clause;

struct Var {
  int level;            // decision level
  int trail;            // trail level
  Clause * reason;      // implication graph edge through clause
};

};

#endif
