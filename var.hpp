#ifndef _var_hpp_INCLUDED
#define _var_hpp_INCLUDED

namespace CaDiCaL {

struct Var {

  int level;            // decision level
  int trail;            // trail level

  bool seen;            // analyzed in 'analyze' and will be bumped
  bool poison;          // can not be removed during clause minimization
  bool removable;       // can be removed during clause minimization

  int prev, next;       // double links for decision VMTF queue
  long bumped;          // enqueue time stamp for VMTF queue

  Clause * reason;      // implication graph edge

  Var () :
    seen (false), poison (false), removable (false),
    prev (0), next (0), bumped (0)
  { }
};


};

#endif
