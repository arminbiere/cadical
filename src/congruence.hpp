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
    return lhs->rhs == rhs->rhs && lhs->tag == rhs->tag;
  }
};
struct Closure {
    
  Closure (Internal *i) : internal (i) {}
  Internal *internal;
  std::vector<Clause *> binaries;

  std::vector<bool> scheduled;
  std::vector<signed char> marks;
  std::vector<uint64_t> mu1_ids;
  std::vector<uint64_t> mu2_ids;
  std::vector<uint64_t> mu4_ids;

  std::vector<int> lits; // result of definitions
  std::vector<int> rhs; // stack for storing RHS


  void unmark_all ();
  std::vector<int> representant; // union-find
  int & representative (int lit);
  int representative (int lit) const;
  int find_representative(int lit) const;
  void add_binary_clause (int a, int b);
  bool merge_literals (int lit, int other);

  std::vector<uint64_t> lrat_chain;
  void push_lrat_id (const Clause *const c);
  void push_lrat_unit (int lit);
  
  void init_closure();
  void extract_and_gates (Closure&);
  void extract_gates ();
  std::unordered_set<Gate*, Hash, GateEqualTo> table;
  void extract_and_gates_with_base_clause (Clause *c);

  Gate* find_and_lits (unsigned, unsigned);
  void init_and_gate_extraction ();
  Gate* find_first_and_gate (int lhs);
  Gate *find_remaining_and_gate (int lhs);
  void extract_and_gates ();


  
  void extract_congruence ();
  
  Gate* new_and_gate(int);

  bool learn_congruence_unit(int unit);

  void find_units();


  

  
  // we define our own wrapper as cadical has otherwise a non-compatible marking system
  signed char& marked (int lit);
  void mu1 (int lit, Clause *c);
  void mu2 (int lit, Clause *c);
  void mu4 (int lit, Clause *c);
  uint64_t marked_mu1(int lit);
  uint64_t marked_mu2(int lit);
  uint64_t marked_mu4(int lit);
  
  // negbincount (lit) -> noccs (-lit)
};

} // namespace CaDiCaL

#endif