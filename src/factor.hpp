#ifndef _factor_hpp_INCLUDED
#define _factor_hpp_INCLUDED

#include "heap.hpp"

namespace CaDiCaL {

struct Internal;

struct Factorizor {
  Factorizor () {}
  ~Factorizor () {}

  vector<Clause *> delete_later;
  vector<vector<Clause *>> occurs;
  vector<int> common;
  // TODO schedule
};


struct Quotient {
  size_t id;
  struct quotient *prev, *next;
  unsigned factor;
  statches clauses;
  sizes matches;
  size_t matched;
};

struct Scores {
  double *score;
  unsigneds scored;
};

struct Factoring {
  size_t size, allocated;
  unsigned initial;
  unsigned *count;
  scores *scores;
  unsigned bound;
  unsigneds fresh;
  unsigneds counted;
  unsigneds nounted;
  references qlauses;
  uint64_t limit;
  struct {
    quotient *first, *last;
  } quotients;
  heap schedule;  // TODO check block.hpp for reference
};

} // namespace CaDiCaL

#endif
