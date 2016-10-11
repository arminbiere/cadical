#include "format.hpp"

#include <cstring>
#include <cstdarg>
#include <cstdio>

namespace CaDiCaL {

void Format::enlarge () {
  char * old = buffer;
  buffer = new char[size = size ? 2*size : 1];
  memcpy (buffer, old, count);
  delete [] old;
}

inline void Format::push_char (char ch) {
  if (size == count) enlarge ();
  buffer[count++] = ch;
}

void Format::push_string (const char * s) {
  char ch;
  while ((ch = *s++)) push_char (ch);
}

void Format::push_int (int d) {
  char tmp[12];
  sprintf (tmp, "%d", d);
  push_string (tmp);
}

const char * Format::append (const char * fmt, ...) {
  const char * p = fmt;
  va_list ap;
  char ch;
  va_start (ap, fmt);
  while ((ch = *p++)) {
    if (ch != '%') push_char (ch);
    else if (*p == 'c') push_char (va_arg (ap, int)), p++;
    else if (*p == 'd') push_int (va_arg (ap, int)), p++;
    else if (*p == 's') push_string (va_arg (ap, const char*)), p++;
    else { push_char ('%'); push_char (*p); break; }  // unsupported
  }
  va_end (ap);
  push_char (0);
  count--;        // thus automatic append in subsequent calls.
  return buffer;
}

};
