#ifndef _format_hpp_INCLUDED
#define _format_hpp_INCLUDED

#include <cstdarg>

namespace CaDiCaL {

// This class provides a 'printf' string formatting utility.
// Only '%c', '%d', '%s' are supported at this time.
// It is used to capture and save error message.

class Format {
  char * buffer;
  long count, size;
  void enlarge ();
  void push_char (char);
  void push_string (const char *);
  void push_int (int);
  const char * add (const char * fmt, va_list &);
public:
  Format () : buffer (0), count (0), size (0) { }
  ~Format () { if (buffer) delete [] buffer; }
  const char * init (const char * fmt, ...);
  const char * append (const char * fmt, ...);
  operator const char * () const { return count ? buffer : 0; }
};

}

#endif
