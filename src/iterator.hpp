#ifndef _iterator_hpp_INCLUDED
#define _iterator_hpp_INCLUDED

#include <cassert>
#include <vector>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

using namespace std;

struct Watch;
class Clause;

/*------------------------------------------------------------------------*/

// short cuts for iterators over 'int', clause and watch vectors

typedef vector<int>::iterator                      int_iterator;
typedef vector<int>::const_iterator          const_int_iterator;

typedef vector<Clause *>::iterator              clause_iterator;
typedef vector<Clause *>::const_iterator  const_clause_iterator;

typedef vector<Watch>::iterator                  watch_iterator;
typedef vector<Watch>::const_iterator      const_watch_iterator;

typedef int *                                  literal_iterator;
typedef const int *                      const_literal_iterator;

/*------------------------------------------------------------------------*/

class VarIdxIterator {
  int & last;
  int start;
  int max_var;
public:
  VarIdxIterator (int & l, int m) : last (l), start (0), max_var (m) {
    assert (max_var >= 0);
    if (!max_var) start = 1, last = 0;
  }
  int next () {
    if (++last > max_var) last = 1;
    if (last == start) return 0;
    assert (1 <= last), assert (last <= max_var);
    if (!start) start = last;
    return last;
  }
};

/*------------------------------------------------------------------------*/

}

#endif
