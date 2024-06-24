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

enum class Gate_Type {And_Gate, XOr_Gate, ITE_Gate};
struct Gate {
  unsigned lhs;
  Gate_Type tag;
  bool garbage : 1;
  bool indexed : 1;
  bool marked : 1;
  bool shrunken : 1;
  unsigned arity : LD_MAX_ARITY;
  vector<uint64_t> ids;
  vector<int>rhs;

  bool operator == (Gate const& lhs)
  {
    return tag == lhs.tag && rhs == lhs.rhs; 
  }

};

typedef vector<Gate *> GOccs;

static size_t hash_lits (vector<int> lits) {
  size_t hash = 0;
  for (auto lit : lits)
    hash ^= lit;
  return hash;
}
struct Hash {
  size_t operator() (const Gate *const g) const {
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
  vector<Clause *> binaries;

  vector<bool> scheduled;
  vector<signed char> marks;
  vector<uint64_t> mu1_ids;
  vector<uint64_t> mu2_ids;
  vector<uint64_t> mu4_ids;

  vector<int> lits; // result of definitions
  vector<int> rhs; // stack for storing RHS
  vector<int> unsimplified; // stack for storing unsimplified version (XOR, ITEs) for DRAT proof
  vector<int> chain;
  vector<uint64_t> glargecounts; // count for large clauses to complement internal->noccs
  vector<uint64_t> gnew_largecounts; // count for large clauses to complement internal->noccs
  uint64_t& new_largecounts(int lit);
  uint64_t& largecounts(int lit);

  void unmark_all ();
  vector<int> representant; // union-find
  int & representative (int lit);
  int representative (int lit) const;
  int find_representative(int lit) const;
  void add_binary_clause (int a, int b);
  bool merge_literals (int lit, int other);

  // proof production
  vector<uint64_t> lrat_chain;
  void push_lrat_id (const Clause *const c);
  void push_lrat_unit (int lit);


  // occs
  vector<GOccs> gtab;
  GOccs &goccs (int lit);
  void connect_goccs (Gate *g, int lit);
  vector<Gate*> garbage;
  void mark_garbage(Gate*);

  // second counter for size, complements noccs
  uint64_t &largecount (int lit);

  // simplification
  bool skip_and_gate (Gate *g);
  void update_and_gate (Gate *g, int falsified = 0, int clashing = 0);
  void shrink_and_gate (Gate *g, int falsified = 0, int clashing = 0);
  bool simplify_gate (Gate *g);
  void simplify_and_gate (Gate *g);
  bool simplify_gates (int lit);

  bool rewrite_gates(int dst, int src);
  bool rewrite_gate(Gate *g, int dst, int src);
  void rewrite_and_gate(Gate *g, int dst, int src);
  
  size_t units;         // next trail position to propagate
  bool propagate_unit(int lit);
  bool propagate_units();
  size_t propagate_units_and_equivalences();
  bool propagate_equivalence(int lit);
  
  // gates
  void init_closure();
  void extract_and_gates (Closure&);
  void extract_gates ();
  unordered_set<Gate*, Hash, GateEqualTo> table;
  void extract_and_gates_with_base_clause (Clause *c);

  Gate* find_and_lits (int, const vector<int> &rhs);

  void init_xor_gate_extraction (std::vector<Clause *> &candidates);
  void add_xor_matching_proof_chain(Gate *g, int lhs1, int lhs2);
  Gate* find_xor_lits (int, const vector<int> &rhs);
  void extract_xor_gates ();
  void extract_xor_gates_with_base_clause (Clause *c);
  Clause *find_large_xor_side_clause (std::vector<int> &lits);
  
  void init_and_gate_extraction ();
  Gate* find_first_and_gate (int lhs);
  Gate *find_remaining_and_gate (int lhs);
  void extract_and_gates ();


  
  void extract_congruence ();
  
  Gate* new_and_gate(int);
  Gate* new_xor_gate(int);
  //check
  void check_xor_gate_implied (Gate const *const);
  void check_ternary (int a, int b, int c);

  bool learn_congruence_unit(int unit);

  void find_units();
  void find_equivalences();


  // schedule
  vector<int> schedule;
  void schedule_literal(int lit);

  // proof
  void simplify_and_add_to_proof_chain (vector<int> &unsimplified,
                                            vector<int> &chain);
  

  
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