#include "app.hpp"
#include "cadical.hpp"

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

int App::main (int arg, char ** argv) {
  return 0;
}

};
