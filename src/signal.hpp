#ifndef _signal_hpp_INCLUDED
#define _signal_hpp_INCLUDED

namespace CaDiCaL {

class Solver;

class Signal {
  static bool catchedsig;
  static Solver * global_solver;
  static const char * name (int sig);
  static void catchsig (int sig);
public:
  static void reset ();
  static void init (Solver &);
};

};

#endif
