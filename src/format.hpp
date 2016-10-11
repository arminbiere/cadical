#ifndef _format_hpp_INCLUDED
#define _format_hpp_INCLUDED

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
public:
  Format () : buffer (0), count (0), size (0) { } 
  ~Format () { if (buffer) delete [] buffer; }
  const char * generate (const char * fmt, ...);
};

};

#endif
