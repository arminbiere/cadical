#ifndef _app_hpp_INCLUDED
#define _app_hpp_INCLUDED

namespace CaDiCaL {

class Solver;
class Internal;

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
