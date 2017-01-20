#include "internal.hpp"

namespace CaDiCaL {

#ifndef QUIET

// Provide nicely formatted progress report messages while running through
// the 'report' function below.  The code is so complex, because it should
// be easy to add and remove reporting of certain statistics, while at the
// same time proving a nicely looking format, including automatic headers.

/*------------------------------------------------------------------------*/

struct Report {

  const char * header;
  char buffer[20];
  int pos;

  Report (const char * h, int precision, int min, double value);
  Report () { }

  void print_header (char * line);
};

/*------------------------------------------------------------------------*/

void Report::print_header (char * line) {
  int len = strlen (header);
  for (int i = -1, j = pos - (len + 1)/2 - 1; i < len; i++, j++)
    line[j] = i < 0 ? ' ' : header[i];
}

Report::Report (const char * h, int precision, int min, double value)
:
  header (h)
{
  char fmt[10];
  sprintf (fmt, "%%.%df", abs (precision));
  if (precision < 0) strcat (fmt, "%%");
  sprintf (buffer, fmt, value);
  const int min_width = min;
  if (strlen (buffer) >= (size_t) min_width) return;
  sprintf (fmt, "%%%d.%df", min_width, abs (precision));
  if (precision < 0) strcat (fmt, "%%");
  sprintf (buffer, fmt, value);
}

/*------------------------------------------------------------------------*/

// The following statistics are printed in columns, whenever 'report' is
// called.  For instance 'reduce' with prefix '-' will call it.  The other
// more interesting report is due to learning a unit, called iteration, with
// prefix 'i'.  To add another statistics column, add a corresponding line
// here.  If you want to report something else add 'report (..)' functions.

#define REPORTS \
/*     HEADER, PRECISION, MIN, VALUE */ \
REPORT("seconds",      2, 5, process_time ()) \
REPORT("MB",           0, 2, current_resident_set_size () / (double)(1l<<20)) \
REPORT("level",        1, 4, jump_avg) \
REPORT("reductions",   0, 2, stats.reductions) \
REPORT("restarts",     0, 4, stats.restarts) \
REPORT("conflicts",    0, 5, stats.conflicts) \
REPORT("redundant",    0, 5, stats.redundant) \
REPORT("glue",         1, 3, slow_glue_avg) \
REPORT("size",         1, 4, size_avg) \
REPORT("irredundant",  0, 4, stats.irredundant) \
REPORT("variables",    0, 3, active_variables ()) \
REPORT("remaining",   -1, 4, percent (active_variables (), external->max_var)) \

#if 0

// These are some more interesting statistics ...

REPORT("bumplast",    -1, 4, percent (stats.bumplast, stats.bumped)) \
REPORT("propdec",     0, 2, relative (stats.propagations, stats.decisions)) \
REPORT("propconf",    0, 2, relative (stats.propagations, stats.conflicts)) \
REPORT("glue-fast",    1, 4, fast_glue_avg) \
REPORT("propconf",    0, 2, relative (stats.propagations, stats.conflicts)) \
REPORT("blocked",      0, 2, stats.redblocked) \

#endif

/*------------------------------------------------------------------------*/

void Internal::report (char type, int verbose) {
  assert (!verbose || !isalpha (type) || isupper (type));
#ifdef LOGGING
  if (!opts.log)
#endif
  if (opts.quiet || (verbose > opts.verbose)) return;
  const int max_reports = 32;
  Report reports[max_reports];
  int n = 0;
#define REPORT(HEAD,PREC,MIN,EXPR) \
  assert (n < max_reports); \
  reports[n++] = Report (HEAD, PREC, MIN, (double)(EXPR));
  REPORTS
#undef REPORT
  if (!(stats.reports++ % 20)) {
    output->put ("c\n");
    int pos = 4;
    for (int i = 0; i < n; i++) {
      int len = strlen (reports[i].buffer);
      reports[i].pos = pos + (len + 1)/2;
      pos += len + 1;
    }
    const int max_line = pos + 20, nrows = 3;
    char line[max_line];
    for (int start = 0; start < nrows; start++) {
      int i;
      for (i = 0; i < max_line; i++) line[i] = ' ';
      line[0] = 'c';
      for (i = start; i < n; i += nrows) reports[i].print_header (line);
      for (i = max_line-1; line[i-1] == ' '; i--) ;
      line[i] = 0;
      output->put (line);
      output->put ('\n');
    }
    output->put ("c\n");
  }
  output->put ("c "), output->put (type);
  for (int i = 0; i < n; i++)
    output->put (' '), output->put (reports[i].buffer);
  output->put ('\n');
  fflush (stdout);
}

#else // ifndef QUIET

void Internal::report (char type, int verbose) { }

#endif

};

