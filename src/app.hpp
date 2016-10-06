#ifndef _app_hpp_INCLUDED
#define _app_hpp_INCLUDED

namespace CaDiCaL {

class Solver;

class App {
  static void usage ();
  static void check_satisfying_assignment (int (Solver::*)(int));
  static void print_witness ();
  static void banner ();
public:
  static int main (int arg, char ** argv);
};

};

#endif
