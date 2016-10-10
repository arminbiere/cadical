#ifndef _avg_hpp_INCLUDED
#define _avg_hpp_INCLUDED

namespace CaDiCaL {

class Solver;

// Cumulative average.

struct AVG {
  double value;
  long count;
  AVG () : value (0), count (0) { }
  operator double () const { return value; }
  void update (Solver *, double y, const char * name);
};

};

#endif
