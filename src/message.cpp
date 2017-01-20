#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/
#ifndef QUIET
/*------------------------------------------------------------------------*/

void Message::vmessage (Internal * internal, const char * fmt, va_list & ap) {
#ifdef LOGGING
  if (!internal->opts.log)
#endif
  if (internal->opts.quiet) return;
  fputs ("c ", stdout);
  vprintf (fmt, ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

void Message::message (Internal * internal, const char * fmt, ...) {
#ifdef LOGGING
  if (!internal->opts.log)
#endif
  if (internal->opts.quiet) return;
  va_list ap;
  va_start (ap, fmt);
  vmessage (internal, fmt, ap);
  va_end (ap);
}

/*------------------------------------------------------------------------*/

void Message::section (Internal * internal, const char * title) {
#ifdef LOGGING
  if (!internal->opts.log)
#endif
  if (internal->opts.quiet) return;
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
#ifdef LOGGING
  if (!internal->opts.log)
#endif
  if (internal->opts.quiet || !internal->opts.verbose) return;
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
#ifdef LOGGING
  if (!internal->opts.log)
#endif
  if (internal->opts.quiet || !internal->opts.verbose) return;
  printf ("c [%s-%ld] ", phase, count);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/
#endif // ifndef QUIET
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

};
