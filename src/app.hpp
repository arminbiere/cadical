#ifndef _app_hpp_INCLUDED
#define _app_hpp_INCLUDED

namespace CaDiCaL {

class Solver;
class Internal;

class App {
  static Solver * solver;
  static Internal * internal;
  static void usage ();
  static void print_witness ();
  static void banner ();
  static bool set (const char*);
public:
  static int main (int arg, char ** argv);
};

};

#endif
