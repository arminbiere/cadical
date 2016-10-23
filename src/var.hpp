#ifndef _var_hpp_INCLUDED
#define _var_hpp_INCLUDED

namespace CaDiCaL {

class Clause;

struct Var {

  int level;            // decision level
  int trail;            // trail level

  Var * prev, * next;   // double links for decision VMTF queue

  Clause * reason;      // implication graph edge through clause

  Var () : prev (0), next (0) { }
};

};

#endif
