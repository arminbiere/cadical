#ifndef _parse_hpp_INCLUDED
#define _parse_hpp_INCLUDED

namespace CaDiCaL {

// Factors out common functions for parsing of DIMACS and solution files.

class File;
class External;
class Internal;

class Parser {

  typedef signed char signed_char;

  Internal * internal;
  External * external;
  File * file;

  void perr (const char * fmt, ...);
  int parse_char ();

  const char * parse_string (const char * str, char prev);
  const char * parse_positive_int (int & ch, int & res, const char * name);
  const char * parse_lit (int & ch, int & lit, const int vars);
  const char * parse_dimacs_non_profiled ();
  const char * parse_solution_non_profiled ();

public:

  Parser (Internal * i, External * e, File * f)
  : internal (i), external (e), file (f)
  { }

  // Parse a DIMACS file.  Return zero if successful. Otherwise parse error.
  // The clauses are added.
  //
  const char * parse_dimacs ();

  // Parse a solution file as used in the SAT competition, e.g., with
  // comment lines 'c ...', a status line 's ...' and value lines 'v ...'.
  // Returns zero if successful. Otherwise a string is returned describing
  // the parse error.  The parsed solution is saved in 'solution' and can be
  // accessed with 'sol (int lit)'.  We use it for checking learned clauses.
  //
  const char * parse_solution ();
};

};

#endif
