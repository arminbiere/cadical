#ifndef _sweep_hpp_INCLUDED
#define _sweep_hpp_INCLUDED

namespace CaDiCaL {

struct Internal;

struct sweep_proof_clause {
  unsigned sweep_id;  // index for sweeper.clauses
  uint64_t cad_id;   // cadical id
  unsigned kit_id;  // kitten id
  bool learned;
  vector<int> literals;
  vector<unsigned> chain;  // lrat
};

struct Sweeper {
  Sweeper (Internal *internal);
  ~Sweeper ();
  Internal *internal;
  Random random;
  vector<unsigned> depths;
  int* reprs;
  vector<int> next, prev;
  int first, last;
  unsigned encoded;
  unsigned save;
  vector<int> vars;
  vector<Clause *> clauses;
  vector<int> clause;
  vector<int> propagate;
  vector<int> backbone;
  vector<int> partition;
  vector<bool> prev_units;
  vector<sweep_proof_clause> core[2];
  uint64_t current_ticks;
  struct {
    uint64_t ticks;
    unsigned clauses, depth, vars;
  } limit;
};

} // namespace CaDiCaL

#endif
