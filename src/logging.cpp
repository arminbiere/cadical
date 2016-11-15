#ifdef LOGGING

#include "internal.hpp"

#include <cstdio>
#include <cstdarg>
#include <algorithm>

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

template<class T, class I>
inline static void log_literals (const T & lits, bool sortit = false) {
  const I end = lits.end ();
  I i = lits.begin ();
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
    else printf (" redundant glue %u analyzed %ld", c->glue, c->analyzed ());
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
