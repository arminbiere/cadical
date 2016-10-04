#ifndef _parse_hpp_INCLUDED
#define _parse_hpp_INCLUDED

namespace CaDiCaL {

class File;
class Solver;

class DimacsParser {
  friend class App;
  File * file;
  Solver & solver;
public:
  DimacsParser (Solver &);
  void parse ();
};

class SolutionParser {
  friend class App;
  File * file;
  Solver & solver;
public:
  SolutionParser (Solver &);
  void parse ();
};

};

#endif
