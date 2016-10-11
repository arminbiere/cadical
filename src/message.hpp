#ifndef _message_h_INCLUDED
#define _message_h_INCLUDED

namespace CaDiCaL {

struct File;
class Internal;

struct Message {
  static void print (Internal *, int verbosity, const char *, ...);
  static void die (Internal *, const char *, ...);
  static void section (Internal *, const char * title);
  static void parse_error (Internal *, File *, const char *, ...);
};

};

#endif
