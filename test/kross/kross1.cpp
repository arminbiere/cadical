extern "C" {
#include "kissat.h"
};

#include "cadical.hpp"

#include <climits>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>

static int verbose;
static const char *argv0;

static void die (const char *fmt, ...)
    __attribute__ ((format (printf, 1, 2)));

static void msg (const char *fmt, ...)
    __attribute__ ((format (printf, 1, 2)));

static void vrb (const char *fmt, ...)
    __attribute__ ((format (printf, 1, 2)));

static void die (const char *fmt, ...) {
  va_list ap;
  fprintf (stderr, "%s: error: ", argv0);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void msg (const char *fmt, ...) {
  va_list ap;
  printf ("%s: ", argv0);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void vrb (const char *fmt, ...) {
  if (!verbose)
    return;
  va_list ap;
  printf ("%s:   ", argv0);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

int main (int argc, char **argv) {
  argv0 = argv[0];
  for (int i = 1; i != argc; i++) {
    const char *arg = argv[i];
    if (!strcmp (arg, "-h")) {
      printf ("usage: %s [ -h | -v ]\n", argv0);
      exit (0);
    } else if (!strcmp (arg, "-v"))
      verbose += (verbose < INT_MIN);
    else
      die ("invalid option '%s' (try '-h')", arg);
  }
  {
    CaDiCaL::Solver c;
    if (verbose > 1)
      c.set ("report", 1);
    if (verbose > 2)
      c.set ("verbose", verbose - 2);
    msg ("Initialized 'CaDiCaL' through 'CaDiCaL::Solver::Solver()'.");
    kissat *k = kissat_init ();
    msg ("Initialized 'Kissat' solver through 'kissat_init()'.");
    if (verbose < 2)
      kissat_set_option (k, "quiet", 1);
    else if (verbose > 2)
      kissat_set_option (k, "verbose", verbose - 2);
    for (int lit : {2, 0, 1, -2, 0, -1, 2, 0}) {
      vrb ("calling 'kissat_add(%d)'", lit), kissat_add (k, lit);
      vrb ("calling 'CaDiCaL::Solver::add(%d)'", lit), c.add (lit);
    }
    msg ("Added CNF to both solvers.");
    vrb ("calling 'kissat_solve()'");
    int r = kissat_solve (k);
    if (r != 10)
      die ("'kissat_solve' returns '%d' but expected '10'", r);
    vrb ("'kissat_solve' returns '10' (as expected)");
    vrb ("calling 'CaDiCaL::Solver::solve()'");
    int s = c.solve ();
    if (s != 10)
      die ("'CaDiCaL::Solver::solve' returns '%d' but expected '10'", s);
    vrb ("'CaDiCaL::Solver::solve' returns '10' (as expected)");
    for (int lit : {1, 2}) {
      int u = kissat_value (k, lit);
      if (u != lit)
        die ("'kissat_value(k,%d)' returns '%d' but expected '%d'", lit, u,
             lit);
      vrb ("'kissat_value(k,%d)' returns '%d' (as expected)", lit, u);
      int v = c.val (lit);
      if (v != lit)
        die ("'CaDiCaL::Solver::val(%d)' returns '%d' but expected '%d'",
             lit, v, lit);
      vrb ("'CaDiCaL::Solver::val(%d)' returns '%d' (as expected)", lit, v);
    }
    msg ("Both solvers produced the same results.");
    vrb ("calling 'kissat_release'");
    kissat_release (k);
    vrb ("calling 'CaDiCaL::Solver::~Solver()'");
  }
  msg ("exit(0)");
  return 0;
}
