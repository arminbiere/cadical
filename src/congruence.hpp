#ifndef _congruenc_hpp_INCLUDED
#define _congruenc_hpp_INCLUDED


#include <array>
#include <cassert>
#include <cstddef>
#include <unordered_map>
#include <unordered_set>
#include <memory>
#include <vector>

#include "util.hpp"
#include "inttypes.hpp"
#include "clause.hpp"

namespace CaDiCaL {
  
#define LD_MAX_ARITY 26
#define MAX_ARITY ((1 << LD_MAX_ARITY) - 1)

struct Internal;

enum class Gate_Type {And_Gate, Or_Gate, ITE_Gate};
struct Gate {
  unsigned lhs;
  Gate_Type tag;
  bool garbage : 1;
  bool indexed : 1;
  bool marked : 1;
  unsigned arity : LD_MAX_ARITY;
  std::vector<uint64_t> ids;
  std::vector<int>rhs;

  bool operator == (Gate const& lhs)
  {
    return tag == lhs.tag && rhs == lhs.rhs; 
  }

};

static std::size_t hash_lits (std::vector<int> lits) {
  std::size_t hash = 0;
  for (auto lit : lits)
    hash ^= lit;
  return hash;
}
struct Hash {
  std::size_t operator() (const Gate *const g) const {
    return hash_lits (g->rhs);
  }
};

struct GateEqualTo {
  bool operator()(const Gate *const lhs, const Gate *const rhs) const 
  {
    return lhs->rhs == rhs->rhs;
  }
};
struct Closure {
    
  Closure (Internal *i) : internal (i) {}
  Internal *internal;
  std::vector<Clause *> binaries;

  std::vector<bool> scheduled;
  std::vector<signed char> marks;

  
  std::vector<int> representative; // union-find
  int find_representative(int lit) const;
  void add_binary_clause (int a, int b);

  std::vector<int> lits; // result of definitions
  std::vector<int> rhs; // stack for storing RHS
  
  void init_closure();
  void extract_and_gates (Closure&);
  void extract_gates (Closure&);
  std::unordered_set<Gate*, Hash, GateEqualTo> table;
  void extract_and_gates_with_base_clause (Clause *c);

  Gate* find_and_lits (unsigned, unsigned);
  bool merge_literals (int lit, int other);
  void init_and_gate_extraction ();
  Gate* find_first_and_gate (int lhs);
  Gate *find_remaining_and_gate (int lhs);
  void extract_and_gates ();
  
  Gate* new_and_gate(int);

  bool learn_congruence_unit(int unit);

  // we define our own wrapper as cadical has otherwise a non-compatible marking system
  signed char& marked (int lit);
  // negbincount (lit) -> noccs (-lit)
};

} // namespace CaDiCaL

#endif