#include "internal.hpp"

#include "macros.hpp"
#include "message.hpp"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdarg>
#include <cassert>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

void Message::vmessage (Internal * internal, const char * fmt, va_list & ap) {
  fputs ("c ", stdout);
  vprintf (fmt, ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

void Message::message (Internal * internal, const char * fmt, ...) {
  va_list ap;
  va_start (ap, fmt);
  vmessage (internal, fmt, ap);
  va_end (ap);
}

/*------------------------------------------------------------------------*/

void Message::verror (Internal * internal, const char *fmt, va_list & ap) {
  fputs ("*** cadical error: ", stderr);
  vfprintf (stderr, fmt, ap);
  fputc ('\n', stderr);
}

void Message::error (Internal * internal, const char *fmt, ...) {
  va_list ap;
  va_start (ap, fmt);
  verror (internal, fmt, ap);
  va_end (ap);                          // unreachable
}

/*------------------------------------------------------------------------*/

void Message::section (Internal * internal, const char * title) {
#ifndef LOGGING
  if (internal->opts.quiet) return;
#endif
  char line[160];
  sprintf (line, "---- [ %s ] ", title);
  assert (strlen (line) < sizeof line);
  int i = 0;
  for (i = strlen (line); i < 76; i++) line[i] = '-';
  line[i] = 0;
  if (internal->stats.sections++) MSG ("");
  MSG (line);
  MSG ("");
}

/*------------------------------------------------------------------------*/

void Message::verbose (Internal * internal,
                       const char * phase,
		       const char * fmt, ...) {
#ifndef LOGGING
  if (internal->opts.quiet) return;
  if (!internal->opts.verbose) return;
#endif
  printf ("c [%s] ", phase);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

void Message::verbose (Internal * internal,
                       const char * phase, long count,
		       const char * fmt, ...) {
#ifndef LOGGING
  if (internal->opts.quiet) return;
  if (!internal->opts.verbose) return;
#endif
  printf ("c [%s-%ld] ", phase, count);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

};
