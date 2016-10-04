#ifndef _parse_hpp_INCLUDED
#define _parse_hpp_INCLUDED

namespace CaDiCaL {

class File;
class Solver;

struct Parser {
protected:
  File & file;
  Parser (File & f) : file (f) { }
  void perr (const char * fmt, ...);
  int parse_char ();
  void parse_string (const char * str, char prev);
  void parse_positive_int (int ch, int & res, const char * name);
  void parse_lit (int ch, int & lit);
};

struct DimacsParser : public Parser {
  Solver & solver;
public:
  DimacsParser (Solver & s, File & f) : Parser (f), solver (s) { }
  static void parse (Solver &, File & file);
};

};

#endif
