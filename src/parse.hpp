#ifndef _parse_hpp_INCLUDED
#define _parse_hpp_INCLUDED

namespace CaDiCaL {

struct File;
class Internal;

class Parser {
  Internal * internal;
  File * file;
  void perr (const char * fmt, ...);
  int parse_char ();
  const char * parse_string (const char * str, char prev);
  const char * parse_positive_int (int & ch, int & res, const char * name);
  const char * parse_lit (int & ch, int & lit);
  const char * parse_dimacs_non_profiled ();
  const char * parse_solution_non_profiled ();
public:
  Parser (Internal * s, File * f) : internal (s), file (f) { }
  const char * parse_dimacs ();
  const char * parse_solution ();
};

};

#endif
