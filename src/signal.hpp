#ifndef _signal_hpp_INCLUDED
#define _signal_hpp_INCLUDED

namespace CaDiCaL {

// Helper class for handling signals in applications.

class Handler {
public:
  Handler () { }
  virtual ~Handler () { }
  virtual void catch_signal (int sig) = 0;
  virtual void catch_alarm ();
};

class Signal {

public:

  static void set (Handler *);
  static void alarm (int seconds);
  static void reset ();
  static void reset_alarm ();

  static const char * name (int sig);
};

}

#endif
