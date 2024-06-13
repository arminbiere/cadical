#ifndef _elim_hpp_INCLUDED
#define _elim_hpp_INCLUDED

#include "heap.hpp" // Alphabetically after 'elim.hpp'.

namespace CaDiCaL {

struct Internal;

struct elim_more {
  Internal *internal;
  elim_more (Internal *i) : internal (i) {}
  bool operator() (unsigned a, unsigned b);
};

typedef heap<elim_more> ElimSchedule;

struct proof_clause {
  uint64_t id;
  vector<int> literals;
  // for lrat
  unsigned cid;  // kitten id
  bool learned;
  vector<uint64_t> chain;
};

struct Eliminator {

  Internal *internal;
  ElimSchedule schedule;

  Eliminator (Internal *i) : internal (i), schedule (elim_more (i)), definition_unit (0) {}
  ~Eliminator ();

  queue<Clause *> backward;

  Clause *dequeue ();
  void enqueue (Clause *);

  vector<Clause *> gates;
  vector<vector<int>> prime_gates;
  unsigned definition_unit;
  vector<proof_clause> proof_clauses;
  vector<int> marked;
};

} // namespace CaDiCaL

#endif
