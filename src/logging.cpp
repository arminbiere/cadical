#ifdef LOGGING

#include "logging.hpp"
#include "clause.hpp"

#include <cstdio>
#include <cstdarg>

namespace CaDiCaL {

void LOG (const char * fmt, ...) {
  va_list ap;
  printf ("c LOG %d ", level);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

void LOG (Clause * c, const char *fmt, ...) {
  va_list ap;
  printf ("c LOG %d ", level);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  if (c) {
    if (!c->redundant) printf (" irredundant");
    else printf (" redundant glue %u resolved %ld", c->glue, c->resolved);
    printf (" size %d clause", c->size);
    for (int i = 0; i < c->size; i++)
      printf (" %d", c->literals[i]);
  } else if (level) printf (" decision");
  else printf (" unit");
  fputc ('\n', stdout);
  fflush (stdout);
}

void LOG (const vector<int> & clause, const char *fmt, ...) {
  va_list ap;
  printf ("c LOG %d ", level);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  for (size_t i = 0; i < clause.size (); i++)
    printf (" %d", clause[i]);
  fputc ('\n', stdout);
  fflush (stdout);
}

};

#endif
