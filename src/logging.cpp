#ifdef LOGGING

#include "internal.hpp"

#include <cstdio>
#include <cstdarg>

namespace CaDiCaL {

void Logger::log (Internal * internal, const char * fmt, ...) {
  va_list ap;
  printf ("c LOG %d ", internal->level);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

void Logger::log (Internal * internal, const Clause * c, const char *fmt, ...) {
  va_list ap;
  printf ("c LOG %d ", internal->level);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  if (c) {
    if (!c->redundant) printf (" irredundant");
    else if (!c->extended) printf (" redundant glue %u", c->glue);
    else printf (" redundant glue %u resolved %ld", c->glue, c->resolved ());
    printf (" size %d clause", c->size);
    for (const_literal_iterator i = c->begin (); i != c->end (); i++)
      printf (" %d", *i);
  } else if (internal->level) printf (" decision");
  else printf (" unit");
  fputc ('\n', stdout);
  fflush (stdout);
}

void Logger::log (Internal * internal,
                  const vector<int> & clause, const char *fmt, ...) {
  va_list ap;
  printf ("c LOG %d ", internal->level);
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
