#ifndef _parse_hpp_INCLUDED
#define _parse_hpp_INCLUDED

namespace CaDiCaL {

class File;
class Solver;

class Parser {
  Solver * solver;
  File * file;
  void perr (const char * fmt, ...);
  int parse_char ();
  void parse_string (const char * str, char prev);
  int parse_positive_int (int ch, int & res, const char * name);
  int parse_lit (int ch, int & lit);
public:
  Parser (Solver * s, File * f) : solver (s), file (f) { }
  void parse_dimacs ();
#ifndef NDEBUG
  void parse_solution ();
#endif
};

};

#endif
