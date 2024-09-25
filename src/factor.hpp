#ifndef _factor_hpp_INCLUDED
#define _factor_hpp_INCLUDED

#include "heap.hpp"

namespace CaDiCaL {

struct Internal;

struct Quotient {
  size_t id;
  Quotient *prev, *next;
  unsigned factor;
  // statches clauses;  // TODO statches?
  vector<size_t> matches;  // TODO sizes type correct?
  size_t matched;
};

struct Scores {
  double *score;
  vector<unsigned> scored;
};

struct Factoring {
  size_t size, allocated;
  unsigned initial;
  unsigned *count;
  Scores *scores;
  unsigned bound;
  vector<unsigned> fresh;
  vector<unsigned> counted;
  vector<unsigned> nounted;
  vector<Clause *> qlauses;
  uint64_t limit;
  struct {
    Quotient *first, *last;
  } quotients;
  // heap schedule;  // TODO check block.hpp for reference
};

} // namespace CaDiCaL

#endif
