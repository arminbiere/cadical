#ifndef _signal_hpp_INCLUDED
#define _signal_hpp_INCLUDED

namespace CaDiCaL {

class Internal;

class Signal {
  static bool catchedsig;
  static Internal * internal;
  static const char * name (int sig);
  static void catchsig (int sig);
public:
  static void reset ();
  static void init (Internal *);
};

};

#endif
