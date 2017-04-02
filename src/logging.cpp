#ifdef LOGGING

#include "internal.hpp"

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

// It is hard to factor out the common part between the two clause loggers,
// since they are also used in slightly different contexts.  Our attempt to
// do so were not more readable than the current version.  See the header
// for an explanation of the difference between the following two functions.

void Logger::log (Internal * internal, const Clause * c, const char *fmt, ...) {
  va_list ap;
  printf ("c LOG %d ", internal->level);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  if (c) {
    if (c->redundant) printf (" redundant glue %d", c->glue);
    else printf (" irredundant");
    printf (" size %d clause", c->size);
    if (internal->opts.logsort) {
      vector<int> s;
      for (const_literal_iterator i = c->begin (); i != c->end (); i++)
        s.push_back (*i);
      sort (s.begin (), s.end (), lit_less_than ());
      for (const_int_iterator i = s.begin (); i != s.end (); i++)
        printf (" %d", *i);
    } else {
      for (const_literal_iterator i = c->begin (); i != c->end (); i++)
        printf (" %d", *i);
    }
    printf (" 0");
  } else if (internal->level) printf (" decision");
  else printf (" unit");
  fputc ('\n', stdout);
  fflush (stdout);
}

// Same as above, but for the global 'clause' (which is not a reason).

void Logger::log (Internal * internal,
                  const vector<int> & c, const char *fmt, ...) {
  va_list ap;
  printf ("c LOG %d ", internal->level);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  if (internal->opts.logsort) {
    vector<int> s;
    for (const_int_iterator i = c.begin (); i != c.end (); i++)
      s.push_back (*i);
    sort (s.begin (), s.end (), lit_less_than ());
    for (const_int_iterator i = s.begin (); i != s.end (); i++)
      printf (" %d", *i);
  } else {
    for (const_int_iterator i = c.begin (); i != c.end (); i++)
      printf (" %d", *i);
  }
  printf (" 0\n");
  fflush (stdout);
}

};

#endif
