#include "app.hpp"
#include "internal.hpp"
#include "cadical.hpp"
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

void App::check_satisfying_assignment (int (Internal::*assignment)(int)) {
  bool satisfied = false;
  size_t start = 0;
  for (size_t i = 0; i < internal->original.size (); i++) {
    int lit = internal->original[i];
    if (!lit) {
      if (!satisfied) {
        fflush (stdout);
        fputs ("*** cadical error: unsatisfied clause:\n", stderr);
        for (size_t j = start; j < i; j++)
          fprintf (stderr, "%d ", internal->original[j]);
        fputs ("0\n", stderr);
        fflush (stderr);
        abort ();
      }
      satisfied = false;
      start = i + 1;
    } else if (!satisfied && (internal->*assignment) (lit) > 0) satisfied = true;
  }
  solver->msg ("satisfying assignment checked");
}

void App::print_witness () {
  int c = 0;
  for (int i = 1; i <= internal->max_var; i++) {
    if (!c) File::print ('v'), c = 1;
    char str[20];
    sprintf (str, " %d", internal->val (i) < 0 ? -i : i);
    int l = strlen (str);
    if (c + l > 78) File::print ("\nv"), c = 1;
    File::print (str);
    c += l;
  }
  if (c) File::print ('\n');
  File::print ("v 0\n");
  fflush (stdout);
}

void App::banner () {
  solver->section ("banner");
  solver->msg ("CaDiCaL Radically Simplified CDCL SAT Internal");
  solver->msg ("Version " VERSION " " GITID);
  solver->msg ("Copyright (c) 2016 Armin Biere, JKU");
  solver->msg (COMPILE);
}

bool App::set (const char * arg) { return internal->opts.set (arg); }

int App::main (int argc, char ** argv) {
  File * dimacs = 0, * proof = 0, * solution = 0;
  bool trace_proof = false, binary_proof = true;
  const char * proof_name = 0;
  int i, res;
  solver = new Solver ();
  internal = solver->internal;
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h")) usage (), exit (0);
    else if (!strcmp (argv[i], "--version"))
      fputs (VERSION "\n", stdout), exit (0);
    else if (!strcmp (argv[i], "-")) {
      if (trace_proof) solver->die ("too many arguments");
      else if (!dimacs) dimacs = File::read (stdin, "<stdin>");
      else trace_proof = true, proof_name = 0;
    } else if (!strcmp (argv[i], "-s")) {
      if (++i == argc) solver->die ("argument to '-s' missing");
      if (solution) solver->die ("multiple solution files");
      if (!(solution = File::read (argv[i])))
        solver->die ("can not read solution file '%s'", argv[i]);
    } else if (!strcmp (argv[i], "-n")) set ("--no-witness");
    else if (!strcmp (argv[i], "-q")) set ("--quiet");
    else if (!strcmp (argv[i], "-v")) set ("--verbose");
    else if (!strcmp (argv[i], "-c")) set ("--check");
    else if (set (argv[i])) { /* nothing do be done */ }
    else if (argv[i][0] == '-') solver->die ("invalid option '%s'", argv[i]);
    else if (trace_proof) solver->die ("too many arguments");
    else if (dimacs) trace_proof = true, proof_name = argv[i];
    else if (!(dimacs = File::read (argv[i])))
      solver->die ("can not open and read DIMACS file '%s'", argv[i]);
  }
  if (solution && !internal->opts.check) set ("--check");
  if (!dimacs) dimacs = File::read (stdin, "<stdin>");
  banner ();
  Signal::init (internal);
  solver->section ("parsing input");
  solver->msg ("reading DIMACS file from '%s'", dimacs->name ());
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
    check_satisfying_assignment (&Internal::sol);
  }
  solver->options ();
  solver->section ("proof tracing");
  if (trace_proof) {
    if (!proof_name) {
      proof = File::write (stdout, "<stdout>");
      if (isatty (1) && internal->opts.binary) {
        solver->msg (
	  "non-binary proof since '<stdout>' connected to terminal");
        binary_proof = false;
      }
    } else if (!(proof = File::write (proof_name)))
      solver->die ("can not open and write DRAT proof to '%s'", proof_name);
    if (binary_proof && !internal->opts.binary) binary_proof = false;
    solver->msg ("writing %s DRAT proof trace to '%s'",
      (binary_proof ? "binary" : "non-binary"), proof->name ());
    internal->proof = new Proof (internal, proof, binary_proof);
  } else solver->msg ("will not generate nor write DRAT proof");
  res = internal->solve ();
  if (proof) { delete proof; internal->proof = 0; }
  solver->section ("result");
  if (res == 10) {
    check_satisfying_assignment (&Internal::val);
    printf ("s SATISFIABLE\n");
    if (internal->opts.witness) print_witness ();
    fflush (stdout);
  } else {
    assert (res = 20);
    printf ("s UNSATISFIABLE\n");
    fflush (stdout);
  }
  Signal::reset ();
  solver->statistics ();
  solver->msg ("exit %d", res);
  if (!internal->opts.leak) delete solver;
  return res;
}

};
