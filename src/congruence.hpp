#ifndef _congruenc_hpp_INCLUDED
#define _congruenc_hpp_INCLUDED


#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <queue>
#include <sys/types.h>
#include <unordered_map>
#include <unordered_set>
#include <memory>
#include <string>
#include <vector>

#include "util.hpp"
#include "inttypes.hpp"
#include "clause.hpp"
#include "watch.hpp"

namespace CaDiCaL {


// This implements the algorithm algorithm from SAT 2024.
//
// The idea is to:
//   0. handle binary clauses
//   1. detect gates and merge gates with same inputs
//   2. eagerly replace the equivalent literals and merge gates with same
//   inputs
//   3. forward subsume
//
// In step 0 the normalization is fully lazy but we do not care about a normal form. Therefore we
// actually eagerly merge literals.
//
// In step 2 there is a subtility: we only replace with the equivalence chain as far as we
// propagated so far. This is the eager part. For LRAT we produce the equivalence up to the point we
// have propagated, no the full chain. This is important for merging literals.  To merge literals we
// use union-find but we only compress paths when rewriting the literal, not before.

struct Internal;

#define LD_MAX_ARITY 26
#define MAX_ARITY ((1 << LD_MAX_ARITY) - 1)

enum class Gate_Type { And_Gate, XOr_Gate, ITE_Gate };
typedef std::pair<int,int> litpair;
typedef std::vector<litpair> litpairs;

std::string string_of_gate (Gate_Type t);

struct LitClausePair {
  int current_lit;  // current literal from the gate
  Clause *clause;
};

LitClausePair make_LitClausePair (int lit, Clause* cl);

struct Gate {
#ifdef LOGGING
  unsigned id;
#endif  
  int lhs;
  Gate_Type tag;
  bool garbage : 1;
  bool indexed : 1;
  bool marked : 1;
  bool shrunken : 1;
  size_t hash; // TODO remove this field (the C++ implementation is caching it anyway)
  vector<uint64_t> units;
  vector<LitClausePair> pos_lhs_ids;
  vector<LitClausePair> neg_lhs_ids;
  vector<int>rhs;

  size_t arity () const {
    return rhs.size();
  }

  bool operator == (Gate const& lhs)
  {
    return tag == lhs.tag && hash == lhs.hash && rhs == lhs.rhs; 
  }

};

typedef vector<Gate *> GOccs;


struct GateEqualTo {
  bool operator()(const Gate *const lhs, const Gate *const rhs) const 
  {
    return lhs->rhs == rhs->rhs && lhs->tag == rhs->tag;
  }
};

struct CompactBinary {
  Clause *clause;
  uint64_t id;
  int lit1, lit2;
};

struct Hash {
  Hash (std::array<int, 16> &ncs) : nonces (ncs){};
  std::array<int, 16> &nonces;
  size_t operator() (const Gate *const g) const;
};

struct Closure {

  Closure (Internal *i) : internal (i), table (128, Hash (nonces)) {
    
  }

  Internal *const internal;
  vector<CompactBinary> binaries;
  std::vector<std::pair<size_t,size_t>> offsetsize;
  bool full_watching = false;
  std::array<int, 16> nonces;
  typedef unordered_set<Gate *, Hash, GateEqualTo> GatesTable;

  vector<bool> scheduled;
  vector<signed char> marks;
  vector<LitClausePair> mu1_ids, mu2_ids, mu4_ids; // remember the ids and the literal

  vector<int> lits; // result of definitions
  vector<int> rhs; // stack for storing RHS
  vector<int> unsimplified; // stack for storing unsimplified version (XOR, ITEs) for DRAT proof
  vector<int> chain;
  vector<uint64_t> glargecounts; // count for large clauses to complement internal->noccs
  vector<uint64_t> gnew_largecounts; // count for large clauses to complement internal->noccs
  GatesTable table;
  std::array<std::vector<std::pair<int, int>>, 2> condbin;
  std::array<std::vector<std::pair<int, int>>, 2> condeq;

  std::vector<Clause*> new_unwatched_binary_clauses;
#ifdef LOGGING
  unsigned fresh_id;
#endif  

  uint64_t& new_largecounts(int lit);
  uint64_t& largecounts(int lit);

  void unmark_all ();
  vector<int> representant; // union-find
  vector<int> eager_representant; // union-find
  vector<uint64_t> eager_representant_id; // lrat version of union-find
  int & representative (int lit);
  int representative (int lit) const;
  int & eager_representative (int lit);
  int eager_representative (int lit) const;
  int find_representative (int lit);
  int find_representative_and_update_eager (int lit);
  int find_eager_representative_and_compress (int);
  void find_eager_representative_and_compress_both (int); // generates clauses for -lit and lit
  uint64_t & eager_representative_id (int lit);
  uint64_t eager_representative_id (int lit) const;
  uint64_t find_representative_lrat (int lit);
  void produce_representative_lrat (int lit);
  Clause* add_binary_clause (int a, int b);
  bool merge_literals_lrat (Gate *g, Gate *h, int lit, int other, const std::vector<uint64_t>& = {}, const std::vector<uint64_t> & = {});
  bool merge_literals (int lit, int other, bool learn_clauses = true);
  bool merge_literals_equivalence (int lit, int other, uint64_t, uint64_t);

  // proof production
  vector<LitClausePair> lrat_chain;
  void push_lrat_id (const Clause *const c, int lit);
  void push_lrat_unit (int lit);


  // occs
  vector<GOccs> gtab;
  GOccs &goccs (int lit);
  void connect_goccs (Gate *g, int lit);
  vector<Gate*> garbage;
  void mark_garbage(Gate*);
  // remove the gate from the table
  bool remove_gate (Gate*);
  bool remove_gate (GatesTable::iterator git);
  void index_gate (Gate*);

  // second counter for size, complements noccs
  uint64_t &largecount (int lit);

  // simplification
  bool skip_and_gate (Gate *g);
  bool skip_xor_gate (Gate *g);
  void update_and_gate (Gate *g, GatesTable::iterator, int falsified = 0, int clashing = 0, const std::vector<uint64_t>& = {}, const std::vector<uint64_t> & = {});
  void update_xor_gate (Gate *g, GatesTable::iterator);
  void shrink_and_gate (Gate *g, int falsified = 0, int clashing = 0);
  bool simplify_gate (Gate *g);
  void simplify_and_gate (Gate *g);
  void simplify_ite_gate (Gate *g);
  void simplify_xor_gate (Gate *g);
  bool simplify_gates (int lit);

  //rewriting
  bool rewriting_lhs (Gate *g, int dst);
  bool rewrite_gates(int dst, int src, uint64_t id1, uint64_t id2);
  bool rewrite_gate(Gate *g, int dst, int src, uint64_t id1, uint64_t id2);
  void rewrite_xor_gate(Gate *g, int dst, int src);
  void rewrite_and_gate(Gate *g, int dst, int src, uint64_t id1, uint64_t id2);
  void rewrite_ite_gate(Gate *g, int dst, int src);
  
  size_t units;         // next trail position to propagate
  bool propagate_unit(int lit);
  bool propagate_units();
  size_t propagate_units_and_equivalences();
  bool propagate_equivalence(int lit);
  
  // gates
  void init_closure();
  void reset_closure();
  void reset_extraction();
  void reset_and_gate_extraction ();
  void extract_and_gates (Closure&);
  void extract_gates ();
  void extract_and_gates_with_base_clause (Clause *c);
  void init_and_gate_extraction ();
  Gate* find_first_and_gate (Clause *base_clause, int lhs);
  Gate *find_remaining_and_gate (Clause *base_clause, int lhs);
  void extract_and_gates ();

  Gate* find_and_lits (const vector<int> &rhs);
  // rhs is sorted, so passing by copy
  Gate* find_gate_lits (const vector<int> &rhs, Gate_Type typ, Gate *except = nullptr);
  Gate* find_xor_lits (const vector<int> &rhs);
  // not const to normalize negations
  Gate* find_ite_lits (vector<int> &rhs, bool&);
  Gate* find_ite_gate (Gate *, bool&);
  Gate* find_xor_gate (Gate *);

  void reset_xor_gate_extraction ();
  void init_xor_gate_extraction (std::vector<Clause *> &candidates);
  uint64_t check_and_add_to_proof_chain (vector<int> &clause);
  void add_xor_matching_proof_chain(Gate *g, int lhs1, int lhs2);
  void add_xor_shrinking_proof_chain(Gate const *const g, int src);
  void extract_xor_gates ();
  void extract_xor_gates_with_base_clause (Clause *c);
  Clause *find_large_xor_side_clause (std::vector<int> &lits);

  void merge_condeq (int cond, litpairs &condeq, litpairs &not_condeq);
  void
  find_conditional_equivalences (int lit,
                                 litpairs &condbin,
                                 litpairs &condeq);
  void
  copy_conditional_equivalences (int lit, litpairs &condbin);
  void check_ite_implied (int lhs, int cond, int then_lit, int else_lit);
  void check_ite_gate_implied (Gate *g);
  void check_and_gate_implied (Gate *g);
  void delete_proof_chain ();

  // ite gate extraction
  void extract_ite_gates_of_literal (int);
  void extract_ite_gates_of_variable (int idx);
  void extract_condeq_pairs (int lit, litpairs &condbin, litpairs &condeq);
  void init_ite_gate_extraction (std::vector<Clause *> &candidates);
  bool find_litpair_second_literal (int lit, litpairs::const_iterator begin,
                                    litpairs::const_iterator end);
  void search_condeq (int lit, int pos_lit,
                             litpairs::const_iterator pos_begin,
                             litpairs::const_iterator pos_end, int neg_lit,
                             litpairs::const_iterator neg_begin,
                             litpairs::const_iterator neg_end,
                             litpairs &condeq);
  void reset_ite_gate_extraction ();
  void extract_ite_gates ();
  

  void forward_subsume_matching_clauses();


  
  void extract_congruence ();
  
  void add_ite_matching_proof_chain(Gate *g, int lhs1, int lhs2);
  void add_ite_turned_and_binary_clauses (Gate *g);
  Gate* new_and_gate(Clause *, int);
  Gate* new_ite_gate (int lhs, int cond, int then_lit, int else_lit);
  Gate* new_xor_gate(int);
  //check
  void check_xor_gate_implied (Gate const *const);
  void check_ternary (int a, int b, int c);
  void check_binary_implied (int a, int b);
  void check_implied ();

  bool learn_congruence_unit(int unit); // TODO remove and replace by _lrat version
  void learn_congruence_unit_falsifies_lrat_chain (Gate *g, int clashing, int unit); 
  void learn_congruence_unit_unit_lrat_chain (Gate *g, int unit); 
  void learn_congruence_unit_when_lhs_set (Gate *g, int lit);

  void find_units();
  void find_equivalences();
  void subsume_clause (Clause *subsuming, Clause *subsumed);
  bool find_subsuming_clause (Clause *c);

  // binary extraction and ternary strengthening
  void extract_binaries ();
  bool find_binary (int, int) const;

  //
  void sort_literals (vector<int> &rhs);

  // schedule
  queue<int> schedule;
  void schedule_literal(int lit);
  void add_clause_to_chain(std::vector<int>, uint64_t);
  // proof. If delete_id is non-zero, then delete the clause instead of learning it
  uint64_t simplify_and_add_to_proof_chain (vector<int> &unsimplified,
                                            vector<int> &chain, uint64_t delete_id = 0);
  

  
  // we define our own wrapper as cadical has otherwise a non-compatible marking system
  signed char& marked (int lit);
  void set_mu1_reason (int lit, Clause *c);
  void set_mu2_reason (int lit, Clause *c);
  void set_mu4_reason (int lit, Clause *c);
  LitClausePair marked_mu1(int lit);
  LitClausePair marked_mu2(int lit);
  LitClausePair marked_mu4(int lit);
  
  // negbincount (lit) -> noccs (-lit)

};

} // namespace CaDiCaL

#endif