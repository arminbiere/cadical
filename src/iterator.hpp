#ifndef _iterator_hpp_INCLUDED
#define _iterator_hpp_INCLUDED

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

using namespace std;

struct Watch;
class Clause;

/*------------------------------------------------------------------------*/

// Short cuts for iterators over 'int', clause and literal vectors.

typedef vector<int>::iterator                      int_iterator;
typedef vector<int>::const_iterator          const_int_iterator;

typedef vector<Clause *>::iterator              clause_iterator;
typedef vector<Clause *>::const_iterator  const_clause_iterator;

/*------------------------------------------------------------------------*/

}

#endif
