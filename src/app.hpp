#ifndef _app_hpp_INCLUDED
#define _app_hpp_INCLUDED

namespace CaDiCaL {

class Internal;

class App {
  static Internal * internal;
  static void usage ();
  static void check_satisfying_assignment (int (Internal::*)(int));
  static void print_witness ();
  static void banner ();
  static bool set (const char*);
public:
  static int main (int arg, char ** argv);
};

};

#endif
