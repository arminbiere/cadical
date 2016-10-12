#ifndef _message_h_INCLUDED
#define _message_h_INCLUDED

#include <cstdarg>

namespace CaDiCaL {

struct File;
class Internal;

struct Message {
  static void err (Internal *, const char *, ...);
  static void err_va_list (Internal *, const char *, va_list &);

  static void section (Internal *, const char * title);

  static void print (Internal *, int verbosity, const char *, ...);
  static void print_va_list (Internal *, int, const char *, va_list &);
};

};

#define PER(FMT,ARGS...) \
do { \
  internal->error.init (\
    "%s:%d: parse error: ", \
    file->name (), (int) file->lineno ()); \
  return internal->error.append (FMT, ##ARGS); \
} while (0)

#endif
