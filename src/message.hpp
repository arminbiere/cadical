#ifndef _message_h_INCLUDED
#define _message_h_INCLUDED

#include <cstdarg>

namespace CaDiCaL {

class Internal;

struct Message {

  static void vmessage (Internal *, const char *, va_list &);
  static void message (Internal *, const char *, ...);

  static void verror (Internal *, const char *, va_list &);
  static void error (Internal *, const char *, ...);

  static void section (Internal *, const char * title);

  static void verbose (Internal *,
                       const char * phase,
                       const char *, ...);

  static void verbose (Internal *,
                       const char * phase, long count,
                       const char *, ...);
};

};

#endif
