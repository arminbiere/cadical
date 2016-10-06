#include "app.hpp"
#include "solver.hpp"
#include "../build/config.hpp"

#include <cstring>

namespace CaDiCaL {

Solver * solver;

void App::usage () {
  fputs (
"usage: cadical [ <option> ... ] [ <input> [ <proof> ] ]\n"
"\n"
"where '<option>' is one of the following short options\n"
"\n"
"  -h         print this command line option summary\n"
"  -n         do not print witness\n"
"  -q         quiet (same as '--quiet')\n"
"  -v         more verbose messages (same as '--verbose')\n"
#ifndef NDEBUG
"  -s <sol>   read solution in competition output format\n"
"             (used for testing and debugging only)\n"
#endif
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
"Note that decimal integers are casted to 'double' and 'bool'\n"
"in the natural way, e.g., '1' is interpreted as 'true'.\n"
"\n"
"Then '<input>' is a (compressed) DIMACS file and '<output>'\n"
"is a file to store the DRAT proof.  If no '<proof>' file is\n"
"specified, then no proof is generated.  If no '<input>' is given\n"
"then '<stdin>' is used. If '-' is used as '<input>' then the\n"
"solver reads from '<stdin>'.  If '-' is specified for '<proof>'\n"
"then the proof is generated and printed to '<stdout>'.\n",
  stdout);
}

#ifndef NDEBUG

void App::check_satisfying_assignment (int (Solver::*assignment)(int)) {
  bool satisfied = false;
  size_t start = 0;
  for (size_t i = 0; i < solver->original_literals.size (); i++) {
    int lit = solver->original_literals[i];
    if (!lit) {
      if (!satisfied) {
        fflush (stdout);
        fputs ("*** cadical error: unsatisfied clause:\n", stderr);
        for (size_t j = start; j < i; j++)
          fprintf (stderr, "%d ", solver->original_literals[j]);
        fputs ("0\n", stderr);
        fflush (stderr);
        abort ();
      }
      satisfied = false;
      start = i + 1;
    } else if (!satisfied && (solver->*assignment) (lit) > 0) satisfied = true;
  }
  MSG ("satisfying assignment checked");
}

#endif

void App::print_witness () {
  int c = 0;
  for (int i = 1; i <= solver->max_var; i++) {
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

void App::banner () {
  SECTION ("banner");
  MSG ("CaDiCaL Radically Simplified CDCL SAT Solver");
  MSG ("Version " VERSION " " GITID);
  MSG ("Copyright (c) 2016 Armin Biere, JKU");
  MSG (COMPILE);
}

int App::main (int arg, char ** argv) {
  return 0;
}

};
