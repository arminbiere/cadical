#include "app.hpp"
#include "internal.hpp"
#include "cadical.hpp"
#include "signal.hpp"

#include "../build/config.hpp"

#include <cstring>

extern "C" {
#include "unistd.h"     // for 'isatty'
};

namespace CaDiCaL {

// Static non-reentrant global solver needed for signal handling.

Solver * App::solver;
Internal * App::internal;

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
  Options::usage ();
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
  File * dimacs = 0, * solution = 0;
  const char * proof_name = 0;
  bool trace_proof = false;
  int i, res = 0;
  solver = new Solver ();
  Signal::init (solver);
  internal = solver->internal;
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h")) { usage (); goto DONE; }
    else if (!strcmp (argv[i], "--version")) {
      fputs (CADICAL_VERSION "\n", stdout); goto DONE;
    } else if (!strcmp (argv[i], "-")) {
      if (trace_proof) ERROR ("too many arguments");
      else if (!dimacs) dimacs = File::read (stdin, "<stdin>");
      else trace_proof = true, proof_name = 0;
    } else if (!strcmp (argv[i], "-s")) {
      if (++i == argc) ERROR ("argument to '-s' missing");
      else if (solution) ERROR ("multiple solution files");
      else if (!(solution = File::read (argv[i])))
        ERROR ("can not read solution file '%s'", argv[i]);
    } else if (!strcmp (argv[i], "-n")) set ("--no-witness");
    else if (!strcmp (argv[i], "-q")) set ("--quiet");
    else if (!strcmp (argv[i], "-v")) set ("--verbose");
    else if (!strcmp (argv[i], "-c")) set ("--check");
    else if (set (argv[i])) { /* nothing do be done */ }
    else if (argv[i][0] == '-') ERROR ("invalid option '%s'", argv[i]);
    else if (trace_proof) ERROR ("too many arguments");
    else if (dimacs) trace_proof = true, proof_name = argv[i];
    else if (!(dimacs = File::read (argv[i])))
      ERROR ("can not open and read DIMACS file '%s'", argv[i]);
  }
  if (solution && !solver->get ("check")) solver->set ("check", 1);
  if (!dimacs) dimacs = File::read (stdin, "<stdin>");
  solver->banner ();
  solver->section ("parsing input");
  solver->msg ("reading DIMACS file from '%s'", dimacs->name ());
{
  Parser dimacs_parser (internal, dimacs);
  const char * err = dimacs_parser.parse_dimacs ();
  if (err) { fprintf (stderr, "%s\n", err); exit (1); }
  delete dimacs;
  if (solution) {
    solver->section ("parsing solution");
    Parser solution_parser (internal, solution);
    solver->msg ("reading solution file from '%s'", solution->name ());
    err = solution_parser.parse_solution ();
    if (err) { fprintf (stderr, "%s\n", err); exit (1); }
    delete solution;
    internal->check (&Internal::sol);
  }
}
  solver->options ();
  solver->section ("proof tracing");
  if (trace_proof) {
    if (!proof_name) {
      if (isatty (1) && solver->get ("binary")) {
        solver->msg (
	  "forced non-binary proof since '<stdout>' connected to terminal");
	solver->set ("binary", false);
      }
      solver->proof (stdout, "<stdout>");
    } else if (!solver->proof (proof_name))
      ERROR ("can not open and write DRAT proof to '%s'", proof_name);
    else
      solver->msg ("writing %s DRAT proof trace to '%s'",
	(solver->get ("binary") ? "binary" : "non-binary"), proof_name);
  } else solver->msg ("will not generate nor write DRAT proof");
  res = solver->solve ();
  if (trace_proof) solver->close ();
  solver->section ("result");
  if (res == 10) {
    printf ("s SATISFIABLE\n");
    if (solver->get ("witness")) witness ();
    fflush (stdout);
  } else {
    assert (res = 20);
    printf ("s UNSATISFIABLE\n");
    fflush (stdout);
  }
  solver->statistics ();
DONE:
  Signal::reset ();
  if (!solver->get ("leak")) delete solver;
  printf ("c return %d\n", res);
  fflush (stdout);
  return res;
}

};
