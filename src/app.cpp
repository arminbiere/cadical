#include "app.hpp"
#include "cadical.hpp"
#include "signal.hpp"
#include "file.hpp"

#include "../build/config.hpp"

#include <cstring>

extern "C" {
#include "unistd.h"     // for 'isatty'
};

namespace CaDiCaL {

// Static non-reentrant global solver needed for signal handling.

Solver * App::solver;

void App::usage () {
  fputs (
"usage: cadical [ <option> ... ] [ <input> [ <proof> ] ]\n"
"\n"
"where '<option>' is one of the following short options\n"
"\n"
"  -h         print this command line option summary\n"
"  -n         do not print witness (same as '--no-witness')\n"
"  -v         more verbose messages (same as '--verbose')\n"
"  -q         quiet (same as '--quiet')\n"
"\n"
"  -c         check witness on formula (same as '--check')\n"
"\n"
"  -s <sol>   read solution in competition output format\n"
"             to check consistency of learned clauses\n"
"             during testing and debugging (implies '-c')\n"
"\n"
"or '<option>' can be one of the following long options\n"
"\n",
  stdout);
  solver->usage ();
fputs (
"\n"
"The long options have their default value printed in brackets\n"
"after their description.  They can also be used in the form\n"
"'--<name>' which is equivalent to '--<name>=1' and in the form\n"
"'--no-<name>' which is equivalent to '--<name>=0'.\n"
"\n"
"Then '<input>' has to be a DIMACS file and in '<output>' a DRAT\n"
"proof is saved.  If no '<proof>' file is specified, then no proof\n"
"is generated.  If no '<input>' is given then '<stdin>' is used.\n"
"If '-' is used as '<input>' then the solver reads from '<stdin>'.\n"
"If '-' is specified for '<proof> then a proof is generated and\n"
"printed to '<stdout>'.  The proof is by default stored in binary\n"
"format unless '--binary=0' or the proof is written to '<stdout>'\n"
"and '<stdout>' is connected to a terminal.\n"
"\n"
"The input is assumed to be compressed if it is given explicitly\n"
"and has a '.gz', '.bz2' or '.7z' suffix.  The same applies to the\n"
"output file.  For decompression commands 'gunzip', 'bzcat' and '7z'\n"
"are needed, and for compression 'gzip', 'bzip2' and '7z'.\n",
  stdout);
}

void App::witness () {
  int c = 0, m = solver->max ();
  for (int i = 1; i <= m; i++) {
    if (!c) File::print ('v'), c = 1;
    char str[20];
    sprintf (str, " %d", solver->val (i) < 0 ? -i : i);
    int l = strlen (str);
    if (c + l > 78) File::print ("\nv"), c = 1;
    File::print (str);
    c += l;
  }
  if (c) File::print ('\n');
  File::print ("v 0\n");
  fflush (stdout);
}

bool App::set (const char * arg) { return solver->set (arg); }

#define ERROR(FMT,ARGS...) \
do { solver->err (FMT,##ARGS); res = 1; goto DONE; } while (0)

int App::main (int argc, char ** argv) {
  const char * proof_path = 0, * solution_path = 0, * dimacs_path = 0;
  bool proof_specified = false, dimacs_specified = false;
  const char * dimacs_name;
  const char * err;
  int i, res = 0;
  solver = new Solver ();
  Signal::init (solver);
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h")) { usage (); goto DONE; }
    else if (!strcmp (argv[i], "--version")) {
      fputs (CADICAL_VERSION "\n", stdout); goto DONE;
    } else if (!strcmp (argv[i], "-")) {
      if (proof_specified) ERROR ("too many arguments");
      else if (!dimacs_specified) dimacs_specified = true;
      else                         proof_specified = true;
    } else if (!strcmp (argv[i], "-s")) {
      if (++i == argc) ERROR ("argument to '-s' missing");
      else if (solution_path) ERROR ("multiple solution files");
      else solution_path = argv[i];
    } else if (!strcmp (argv[i], "-n")) set ("--no-witness");
    else if (!strcmp (argv[i], "-q")) set ("--quiet");
    else if (!strcmp (argv[i], "-v")) set ("--verbose");
    else if (!strcmp (argv[i], "-c")) set ("--check");
    else if (set (argv[i])) { /* nothing do be done */ }
    else if (argv[i][0] == '-') ERROR ("invalid option '%s'", argv[i]);
    else if (proof_specified) ERROR ("too many arguments");
    else if (dimacs_specified)
          proof_specified = true, proof_path = argv[i];
    else dimacs_specified = true, dimacs_path = argv[i];
  }
  if (solution_path && !solver->get ("check")) solver->set ("check", 1);
  solver->section ("banner");
  solver->banner ();
  solver->section ("parsing input");
  dimacs_name = dimacs_path ? dimacs_path : "<stdin>";
  solver->msg ("reading DIMACS file from '%s'", dimacs_name);
  if (dimacs_path) err = solver->dimacs (dimacs_path);
  else             err = solver->dimacs (stdin, dimacs_name);
  if (err) ERROR ("%s", err);
  if (solution_path) {
    solver->section ("parsing solution");
    solver->msg ("reading solution file from '%s'", solution_path);
    if ((err = solver->solution (solution_path))) ERROR ("%s", err);
  }
  solver->section ("options");
  solver->options ();
  solver->section ("proof tracing");
  if (proof_specified) {
    if (!proof_path) {
      if (isatty (1) && solver->get ("binary")) {
        solver->msg (
	  "forced non-binary proof since '<stdout>' connected to terminal");
	solver->set ("binary", false);
      }
      solver->proof (stdout, "<stdout>");
    } else if (!solver->proof (proof_path))
      ERROR ("can not open and write DRAT proof to '%s'", proof_path);
    else
      solver->msg ("writing %s DRAT proof trace to '%s'",
	(solver->get ("binary") ? "binary" : "non-binary"), proof_path);
  } else solver->msg ("will not generate nor write DRAT proof");
  res = solver->solve ();
  if (proof_specified) solver->close ();
  solver->section ("result");
  if (res == 10) {
    printf ("s SATISFIABLE\n");
    fflush (stdout);
    if (solver->get ("witness")) witness ();
    fflush (stdout);
  } else if (res == 20) {
    printf ("s UNSATISFIABLE\n");
    fflush (stdout);
  } else {
    printf ("c UNKNOWN\n");
    fflush (stdout);
  }
  solver->statistics ();
  solver->msg ("exit %d", res);
DONE:
  Signal::reset ();
  if (!solver->get ("leak")) delete solver;
  return res;
}

};
