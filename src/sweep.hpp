#ifndef _sweep_hpp_INCLUDED
#define _sweep_hpp_INCLUDED

#include "random.hpp"
#include <cstdint>
#include <vector>

namespace CaDiCaL {

struct Internal;

struct sweep_proof_clause {
  unsigned sweep_id; // index for sweeper.clauses
  int64_t cad_id;    // cadical id
  unsigned kit_id;   // citten id
  bool learned;
  std::vector<int> literals;
  std::vector<unsigned> chain; // lrat
};

struct sweep_blocked_clause {
  int64_t id;
  std::vector<int> literals;
};

struct sweep_binary {
  int lit;
  int other;
  int64_t id;
};

struct Clause;

struct Sweeper {
  Sweeper (Internal *internal);
  ~Sweeper ();
  Internal *internal;
  Random random;
  std::vector<unsigned> depths;
  int *reprs;
  std::vector<int> next, prev;
  int first, last;
  unsigned encoded;
  unsigned save;
  std::vector<int> vars;
  std::vector<Clause *> clauses;
  std::vector<sweep_blocked_clause> blocked_clauses;
  std::vector<int> blockable;
  std::vector<int> clause;
  std::vector<int> propagate;
  std::vector<int> backbone;
  std::vector<int> partition;
  std::vector<bool> prev_units;
  std::vector<sweep_binary> binaries;
  std::vector<sweep_proof_clause> core[2];
  uint64_t current_ticks;
  struct {
    uint64_t ticks;
    unsigned clauses, depth, vars;
  } limit;
};

} // namespace CaDiCaL

#endif
