#ifdef LOGGING

#include "cadical.hpp"

#include <cstdio>
#include <cstdarg>

namespace CaDiCaL {

void Logger::log (Solver & solver, const char * fmt, ...) {
  va_list ap;
  printf ("c LOG %d ", solver.level);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

void Logger::log (Solver & solver, Clause * c, const char *fmt, ...) {
  va_list ap;
  printf ("c LOG %d ", solver.level);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  if (c) {
    if (!c->redundant) printf (" irredundant");
    else printf (" redundant glue %u resolved %ld", c->glue, c->resolved);
    printf (" size %d clause", c->size);
    for (int i = 0; i < c->size; i++)
      printf (" %d", c->literals[i]);
  } else if (solver.level) printf (" decision");
  else printf (" unit");
  fputc ('\n', stdout);
  fflush (stdout);
}

void Logger::log (Solver & solver,
                  const vector<int> & clause, const char *fmt, ...) {
  va_list ap;
  printf ("c LOG %d ", solver.level);
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
