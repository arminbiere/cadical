#ifndef _message_h_INCLUDED
#define _message_h_INCLUDED

namespace CaDiCaL {

struct File;
class Internal;

struct Message {
  static void print (Internal *, int verbosity, const char *, ...);
  static void die (Internal *, const char *, ...);
  static void section (Internal *, const char * title);
};

};

#define PER(FMT,ARGS...) \
do { \
  internal->error.append (\
    "%s:%d: parse error: ", \
    file->name (), (int) file->lineno ()); \
  return internal->error.append (FMT, ##ARGS); \
} while (0)

#endif
