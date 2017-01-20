#ifndef _message_h_INCLUDED
#define _message_h_INCLUDED

namespace CaDiCaL {

class Internal;

struct Message {

#ifndef QUIET 

  // Non-verbose messages, e.g., always printed (unless 'quiet' set).
  //
  static void vmessage (Internal *, const char *, va_list &);
  static void message (Internal *, const char *, ...);

  // This is for printing section headers in the form
  //
  //  c ---- [ <title> ] ---------------------
  //
  // nicely aligned (and of course is ignored if 'quiet' is set).
  //
  static void section (Internal *, const char * title);

  // Print verbose message if 'verbose' is set (and not 'quiet').
  // Note that setting 'log' or '-l' force verbose output (and also ignores
  // 'quiet' set to true').  The 'phase' argument is used to print a 'phase'
  // prefix for the message, e.g.,
  //
  //  c [<phase>] ...
  //
  static void verbose (Internal *,
                       const char * phase,
                       const char *, ...);

  // Same as 'verbose' above exception that the prefix gets a count, e.g.,
  //
  //  c [<phase>-<count>] ...
  //
  static void verbose (Internal *,
                       const char * phase, long count,
                       const char *, ...);
#endif

  // Print error messages which are really always printed (even if 'quiet'
  // is set).  This does lead to abort or exit the current process though.
  //
  static void verror (Internal *, const char *, va_list &);
  static void error (Internal *, const char *, ...);
};

};

#endif // ifndef _message_h_INCLUDED
