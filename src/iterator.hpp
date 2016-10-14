#ifndef _iterator_hpp_INCLUDED
#define _iterator_hpp_INCLUDED

namespace CaDiCaL {

struct Watch;
class Clause;

// short cuts for iterators over 'int', clause and watch vectors

typedef vector<int>::iterator                      int_iterator;
typedef vector<int>::const_iterator          const_int_iterator;

typedef vector<Clause *>::iterator              clause_iterator;
typedef vector<Clause *>::const_iterator  const_clause_iterator;

typedef vector<Watch>::iterator                  watch_iterator;
typedef vector<Watch>::const_iterator      const_watch_iterator;

typedef int *                                  literal_iterator;
typedef const int *                      const_literal_iterator;

}

#endif
