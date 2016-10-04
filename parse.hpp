#ifndef _parse_hpp_INCLUDED
#define _parse_hpp_INCLUDED

#include <cstdio>

namespace CaDiCaL {

class Main;
class Solver;

class DimacsParser {
  friend class Main;
  FILE * input_file, * dimacs_file, * proof_file;
  const char *input_name, *dimacs_name, *proof_name;
  int lineno, close_input, close_proof, trace_proof;
  Solver & solver;
public:
  DimacsParser (Solver &);
  void parse ();
};

class SolutionParser {
  friend class Main;
  FILE * solution_file;
  const char *solution_name;
  int lineno;
  Solver & solver;
public:
  SolutionParser (Solver &);
  void parse ();
};

};

#endif
