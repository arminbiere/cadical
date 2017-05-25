/*------------------------------------------------------------------------*/

// Facade includes only ('internal.hpp' includes all internal headers).

#include "app.hpp"
#include "cadical.hpp"
#include "file.hpp"
#include "signal.hpp"

/*------------------------------------------------------------------------*/

// Need this for the 'banner' information (version etc).

#include <config.hpp>

/*------------------------------------------------------------------------*/

// The only common other 'C' header needed.

#include <cstring>

/*------------------------------------------------------------------------*/

// Internal more specific 'C' header.

extern "C" {
#include "unistd.h"     // for 'isatty'
};

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

// Static non-reentrant global solver needed for signal handling.
//
Solver * App::solver;

/*------------------------------------------------------------------------*/

void App::usage () {
  fputs (
"usage: cadical [ <option> ... ] [ <dimacs> [ <proof> ] ]\n"
"\n"
"where '<option>' is one of the following short options\n"
"\n"
"  -h         print this command line option summary\n"
"  -n         do not print witness (same as '--no-witness')\n"
#ifndef QUIET
"  -v         increase verbose level (see also '--verbose')\n"
"  -q         quiet (same as '--quiet')\n"
#endif
#ifdef LOGGING
"  -l         enable logging messages (same as '--log')\n"
#endif
"  -f         force to read broken DIMACS header (same as '--force')\n"
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
"Then '<dimacs>' has to be a DIMACS file and in '<drat>' a DRAT\n"
"proof is saved.  If no '<proof>' file is specified, then no proof\n"
"is generated.  If no '<dimacs>' is given then '<stdin>' is used.\n"
"If '-' is used as '<dimacs>' then the solver reads from '<stdin>'.\n"
"If '-' is specified for '<proof> then a proof is generated and\n"
"printed to '<stdout>'.  The proof is by default stored in binary\n"
"format unless '--binary=0' or the proof is written to '<stdout>'\n"
"and '<stdout>' is connected to a terminal.\n"
"\n"
"The input is assumed to be compressed if it is given explicitly\n"
"and has a '.gz', '.bz2', '.xz or '.7z' suffix.  The same applies to\n"
"the output file.  For compression and decompression the utilities\n"
"'gzip', 'bzip', '7z', and 'xz' are needed.\n",
  stdout);
}

/*------------------------------------------------------------------------*/

// Pretty print competition format witness with 'v' lines.
//
void App::witness () {
  int c = 0, m = solver->max ();
  File * output = solver->output ();
  for (int i = 1; i <= m; i++) {
    if (!c) output->put ('v'), c = 1;
    char str[20];
    sprintf (str, " %d", solver->val (i) < 0 ? -i : i);
    int l = strlen (str);
    if (c + l > 78) output->put ("\nv"), c = 1;
    output->put (str);
    c += l;
  }
  if (c) output->put ('\n');
  output->put ("v 0\n");
  fflush (stdout);
}

/*------------------------------------------------------------------------*/

// Wrapper around option setting.

bool App::set (const char * arg) { return solver->set (arg); }

/*------------------------------------------------------------------------*/

// Short-cut for errors to avoid a hard 'exit'.

#define ERROR(FMT,ARGS...) \
do { solver->error (FMT,##ARGS); res = 1; goto DONE; } while (0)

/*------------------------------------------------------------------------*/

int App::main (int argc, char ** argv) {
  const char * proof_path = 0, * solution_path = 0, * dimacs_path = 0;
  bool proof_specified = false, dimacs_specified = false;
  const char * dimacs_name, * err;
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
#ifndef QUIET
    else if (!strcmp (argv[i], "-q")) set ("--quiet");
    else if (!strcmp (argv[i], "-v"))
      solver->set ("verbose", solver->get ("verbose") + 1);
#endif
#ifdef LOGGING
    else if (!strcmp (argv[i], "-l")) set ("--log");
#endif
    else if (!strcmp (argv[i], "-c")) set ("--check");
    else if (!strcmp (argv[i], "-f")) set ("--force");
    else if (set (argv[i])) { /* nothing do be done */ }
    else if (argv[i][0] == '-') ERROR ("invalid option '%s'", argv[i]);
    else if (proof_specified) ERROR ("too many arguments");
    else if (dimacs_specified)
          proof_specified = true, proof_path = argv[i];
    else dimacs_specified = true, dimacs_path = argv[i];
  }
  if (dimacs_specified && dimacs_path && !File::exists (dimacs_path))
    ERROR ("DIMACS input file '%s' does not exist", dimacs_path);
  if (solution_path && !File::exists (solution_path))
    ERROR ("solution file '%s' does not exist", solution_path);
  if (solution_path && !solver->get ("check")) set ("--check");
  solver->section ("banner");
  solver->banner ();
  solver->section ("parsing input");
  dimacs_name = dimacs_path ? dimacs_path : "<stdin>";
  solver->message ("reading DIMACS file from '%s'", dimacs_name);
  if (dimacs_path) err = solver->dimacs (dimacs_path);
  else             err = solver->dimacs (stdin, dimacs_name);
  if (err) ERROR ("%s", err);
  if (solution_path) {
    solver->section ("parsing solution");
    solver->message ("reading solution file from '%s'", solution_path);
    if ((err = solver->solution (solution_path))) ERROR ("%s", err);
  }
  solver->section ("options");
  solver->options ();
  solver->section ("proof tracing");
  if (proof_specified) {
    if (!proof_path) {
      if (isatty (1) && solver->get ("binary")) {
        solver->message (
          "forced non-binary proof since '<stdout>' connected to terminal");
        set ("--no-binary");
      }
      solver->message ("writing %s proof trace to '<stdout>'",
        (solver->get ("binary") ? "binary" : "non-binary"));
      solver->proof (stdout, "<stdout>");
    } else if (!solver->proof (proof_path))
      ERROR ("can not open and write DRAT proof to '%s'", proof_path);
    else
      solver->message ("writing %s DRAT proof trace to '%s'",
        (solver->get ("binary") ? "binary" : "non-binary"), proof_path);
  } else solver->message ("will not generate nor write DRAT proof");
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
  solver->message ("exit %d", res);
DONE:
  Signal::reset ();
  if (!solver->get ("leak")) delete solver;
  return res;
}

};
