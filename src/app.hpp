#ifndef _app_hpp_INCLUDED
#define _app_hpp_INCLUDED

namespace CaDiCaL {

class Solver;
class File;

// A wrapper app which makes up the CaDiCaL stand alone solver.  It in
// essence only consists of the 'App::main' function.  So this class
// contains code, which is not required if only the library interface in
// 'Solver' is used.  It further uses static data structures in order to
// have a signal handler catch signals. It is thus neither thread-safe nor
// reentrant.  If you want to use multiple instances of the solver use the
// 'Solver' interface directly (which is thread-safe and reentrant).

class App {

  // Global solver.

  static Solver * solver;

  // Printing.

  static void usage ();
  static void witness ();
  static void banner ();

  // Option handling.

  static bool set (const char*);

public:

  static int main (int arg, char ** argv);
};

};

#endif
