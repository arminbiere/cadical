#include "internal.hpp"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdarg>
#include <cassert>

namespace CaDiCaL {

void Message::print_va_list (Internal * internal,
                             int verbosity, const char * fmt, va_list & ap) {
  if (internal->opts.quiet) return;
  if (internal->opts.verbose < verbosity) return;
  fputs ("c ", stdout);
  vprintf (fmt, ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

void Message::print (Internal * internal,
                     int verbosity, const char * fmt, ...) {
  va_list ap;
  va_start (ap, fmt);
  print_va_list (internal, verbosity, fmt, ap);
  va_end (ap);
}

void Message::err_va_list (Internal * internal,
                           const char *fmt, va_list & ap) {
  fputs ("*** cadical error: ", stderr);
  vfprintf (stderr, fmt, ap);
  fputc ('\n', stderr);
}

void Message::err (Internal * internal, const char *fmt, ...) {
  va_list ap;
  va_start (ap, fmt);
  err_va_list (internal, fmt, ap);
  va_end (ap);				// unreachable
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

};
