#ifndef _signal_hpp_INCLUDED
#define _signal_hpp_INCLUDED

namespace CaDiCaL {

// Helper class for handling signals in 'App'.

class Solver;

class Signal {

  static bool catchedsig;
  static Solver * solver;
  static const char * name (int sig);
  static void catchsig (int sig);

public:

  static void reset ();
  static void init (Solver *);
};

};

#endif
