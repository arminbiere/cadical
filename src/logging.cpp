#ifdef LOGGING

#include "internal.hpp"

namespace CaDiCaL {

void Logger::print_log_prefix (Internal *internal) {
  internal->print_prefix ();
  tout.magenta ();
  fputs ("LOG ", stdout);
  tout.magenta (true);
  printf ("%d ", internal->level);
  tout.normal ();
}

void Logger::log_empty_line (Internal *internal) {
  internal->print_prefix ();
  tout.magenta ();
  const int len = internal->prefix.size (), max = 78 - len;
  for (int i = 0; i < max; i++)
    fputc ('-', stdout);
  fputc ('\n', stdout);
  tout.normal ();
  fflush (stdout);
}

void Logger::log (Internal *internal, const char *fmt, ...) {
  print_log_prefix (internal);
  tout.magenta ();
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  tout.normal ();
  fflush (stdout);
}

// It is hard to factor out the common part between the two clause loggers,
// since they are also used in slightly different contexts.  Our attempt to
// do so were not more readable than the current version.  See the header
// for an explanation of the difference between the following two functions.

void Logger::log (Internal *internal, const Clause *c, const char *fmt,
                  ...) {
  print_log_prefix (internal);
  tout.magenta ();
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  if (c) {
    if (c->redundant)
      printf (" glue %d redundant", c->glue);
    else
      printf (" irredundant");
    printf (" size %d clause[%" PRId64 "]", c->size, c->id);
    if (c->moved)
      printf (" ... (moved)");
    else {
      if (internal->opts.logsort) {
        vector<int> s;
        for (const auto &lit : *c)
          s.push_back (lit);
        sort (s.begin (), s.end (), clause_lit_less_than ());
        for (const auto &lit : s)
          printf (" %d", lit);
      } else {
        for (const auto &lit : *c)
          printf (" %d", lit);
      }
    }
  } else if (internal->level)
    printf (" decision");
  else
    printf (" unit");
  fputc ('\n', stdout);
  tout.normal ();
  fflush (stdout);
}

// Same as above, but for the global clause 'c' (which is not a reason).

void Logger::log (Internal *internal, const vector<int> &c, const char *fmt,
                  ...) {
  print_log_prefix (internal);
  tout.magenta ();
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  if (internal->opts.logsort) {
    vector<int> s;
    for (const auto &lit : c)
      s.push_back (lit);
    sort (s.begin (), s.end (), clause_lit_less_than ());
    for (const auto &lit : s)
      printf (" %d", lit);
  } else {
    for (const auto &lit : c)
      printf (" %d", lit);
  }
  fputc ('\n', stdout);
  tout.normal ();
  fflush (stdout);
}

// Now for 'restore_clause' to avoid copying (without logging).

void Logger::log (Internal *internal,
                  const vector<int>::const_iterator &begin,
                  const vector<int>::const_iterator &end, const char *fmt,
                  ...) {
  print_log_prefix (internal);
  tout.magenta ();
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  if (internal->opts.logsort) {
    vector<int> s;
    for (auto p = begin; p != end; p++)
      s.push_back (*p);
    sort (s.begin (), s.end (), clause_lit_less_than ());
    for (const auto &lit : s)
      printf (" %d", lit);
  } else {
    for (auto p = begin; p != end; p++)
      printf (" %d", *p);
  }
  fputc ('\n', stdout);
  tout.normal ();
  fflush (stdout);
}

// for LRAT proof chains

void Logger::log (Internal *internal, const vector<uint64_t> &c,
                  const char *fmt, ...) {
  print_log_prefix (internal);
  tout.magenta ();
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  for (const auto &id : c)
    printf (" %" PRIu64, id);
  fputc ('\n', stdout);
  tout.normal ();
  fflush (stdout);
}

} // namespace CaDiCaL

#endif
