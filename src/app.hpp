#ifndef _app_hpp_INCLUDED
#define _app_hpp_INCLUDED

namespace CaDiCaL {

class Solver;
class Internal;

// A wrapper app which makes up the CaDiCaL stand alone solver which in
// essence only consists of the 'App::main' function.  So this class
// contains code, which is not required if only the library interface in
// 'Solver' is used.

class App {

  // Global solver.

  static Solver * solver;
  static Internal * internal;

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
