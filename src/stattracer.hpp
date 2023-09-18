#ifndef _stattracer_hpp_INCLUDED
#define _stattracer_hpp_INCLUDED

#include "tracer.hpp"

namespace CaDiCaL {

// Proof tracer class to observer all possible proof events,
// such as added or deleted clauses.
// An implementation can decide on which events to act.

class StatTracer : public Tracer {

public:
  StatTracer () {}
  virtual ~StatTracer () {}
  
  virtual void print_stats () {}

};

} // namespace CaDiCaL

#endif
