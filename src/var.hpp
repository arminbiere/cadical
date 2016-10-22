#ifndef _var_hpp_INCLUDED
#define _var_hpp_INCLUDED

namespace CaDiCaL {

class Clause;

struct Var {

  int level;            // decision level
  int trail;            // trail level

  Var * prev, * next;   // double links for decision VMTF queue
  long bumped;          // enqueue time stamp for VMTF queue

  Clause * reason;      // implication graph edge

  Var () : prev (0), next (0), bumped (0) { }
};


};

#endif
