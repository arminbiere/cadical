#include "internal.hpp"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdarg>
#include <cassert>

namespace CaDiCaL {

void Message::print (Internal * internal,
                     int verbosity, const char * fmt, ...) {
  va_list ap;
  if (internal->opts.quiet) return;
  if (internal->opts.verbose < verbosity) return;
  fputs ("c ", stdout);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

void Message::die (Internal * internal, const char *fmt, ...) {
  va_list ap;
  fputs ("*** cadical error: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

void Message::section (Internal * internal, const char * title) {
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

void Message::parse_error (Internal * internal,
                           File * file, const char * fmt, ...) {
  va_list ap;
  fprintf (stderr,
    "%s:%ld: parse error: ",
    file->name (), file->lineno ());
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

};
