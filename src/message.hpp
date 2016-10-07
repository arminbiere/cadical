#ifndef _message_h_INCLUDED
#define _message_h_INCLUDED

namespace CaDiCaL {

struct File;
class Solver;

struct Message {
  static void print (Solver *, int verbosity, const char *, ...);
  static void die (Solver *, const char *, ...);
  static void section (Solver *, const char * title);
  static void parse_error (Solver *, File *, const char *, ...);
};

};

#endif
