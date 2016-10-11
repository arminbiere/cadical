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
  void parse_string (const char * str, char prev);
  int parse_positive_int (int ch, int & res, const char * name);
  int parse_lit (int ch, int & lit);
public:
  Parser (Internal * s, File * f) : internal (s), file (f) { }
  void parse_dimacs ();
  void parse_solution ();
};

};

#endif
