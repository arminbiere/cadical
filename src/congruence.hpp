#ifndef _congruenc_hpp_INCLUDED
#define _congruenc_hpp_INCLUDED


#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <queue>
#include <sys/types.h>
#include <unordered_set>
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

struct lit_implication {
  int first;
  int second;
  uint64_t id;
  lit_implication (int f, int s, uint64_t _id)
  : first (f), second (s), id (_id) {}
  lit_implication (int f, int s)
  : first (f), second (s), id (0) {}
  lit_implication (): first (0), second (0), id (0) {};
  void swap () {
    std::swap (first, second);
  }
};


struct lit_equivalence {
  int first;
  int second;
  uint64_t first_id;
  uint64_t second_id;
  lit_equivalence (int f, uint64_t f_id, int s, uint64_t s_id)
  : first (f), second (s), first_id (f_id), second_id (s_id) {}
  lit_equivalence (int f, int s)
  : first (f), second (s), first_id (0), second_id (0) {}
  lit_equivalence (): first (0), second (0), first_id (0), second_id (0) {};
  void swap () {
    std::swap (first, second);
    std::swap (first_id, second_id);
  }
};

typedef std::vector<lit_implication> lit_implications;
typedef std::vector<lit_equivalence> lit_equivalences;

std::string string_of_gate (Gate_Type t);

struct LitClausePair {
  int current_lit;  // current literal from the gate
  Clause *clause;
};

LitClausePair make_LitClausePair (int lit, Clause* cl);

struct Gate {
#ifdef LOGGING
  uint64_t id;
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
  bool tautological_clauses;
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

struct Rewrite {
  int src, dst;
  uint64_t id1;
  uint64_t id2;

  Rewrite (int _src, int _dst, uint64_t _id1, uint64_t _id2) : src (_src), dst (_dst),
							       id1 (_id1), id2 (_id2) {};
  Rewrite () : src (0), dst (0), id1 (0), id2 (0) {};
};

struct Closure {

  Closure (Internal *i);

  Internal *const internal;
  vector<CompactBinary> binaries;
  std::vector<std::pair<size_t,size_t>> offsetsize;
  bool full_watching = false;
  std::array<int, 16> nonces;
  typedef unordered_set<Gate *, Hash, GateEqualTo> GatesTable;

  vector<bool> scheduled;
  vector<signed char> marks;
  vector<LitClausePair> mu1_ids, mu2_ids, mu4_ids; // remember the ids and the literal. 2 and 4 are
						   // only used for lrat proofs, but we need 1 to
						   // promote binary clauses to irredundant

  vector<int> lits; // result of definitions
  vector<int> rhs; // stack for storing RHS
  vector<int> unsimplified; // stack for storing unsimplified version (XOR, ITEs) for DRAT proof
  vector<int> chain;
  vector<uint64_t> glargecounts; // count for large clauses to complement internal->noccs
  vector<uint64_t> gnew_largecounts; // count for large clauses to complement internal->noccs
  GatesTable table;
  std::array<lit_implications, 2> condbin;
  std::array<lit_equivalences, 2> condeq;

  std::vector<Clause*> new_unwatched_binary_clauses;
  // LRAT proofs
  vector<signed char> proof_marks;
  vector<int> proof_analyzed;
  vector<signed char> resolvent_marks;
  vector<int> resolvent_analyzed;

#ifdef LOGGING
  uint64_t fresh_id;
#endif  

  uint64_t& new_largecounts(int lit);
  uint64_t& largecounts(int lit);

  void unmark_all ();
  vector<int> representant; // union-find
  vector<int> eager_representant; // union-find
  vector<uint64_t> representant_id; // lrat version of union-find
  vector<uint64_t> eager_representant_id; // lrat version of union-find
  int & representative (int lit);
  int representative (int lit) const;
  int & eager_representative (int lit);
  int eager_representative (int lit) const;
  int find_representative (int lit);
  int find_representative_and_compress (int, bool update_eager = true);
  void find_representative_and_compress_both (int); // generates clauses for -lit and lit
  int find_eager_representative (int);
  int find_eager_representative_and_compress (int);
  void find_eager_representative_and_compress_both (int); // generates clauses for -lit and lit
  uint64_t & eager_representative_id (int lit);
  uint64_t eager_representative_id (int lit) const;
  uint64_t &representative_id (int lit);
  uint64_t representative_id (int lit) const;
  uint64_t find_representative_lrat (int lit);
  uint64_t find_eager_representative_lrat (int lit);
  void produce_eager_representative_lrat (int lit);
  void produce_representative_lrat (int lit);
  Clause* add_binary_clause (int a, int b);

  void promote_clause (Clause *);

  // Merge functions. We actually need different several versions for LRAT in order to simplify the
  // proof production.
  //
  // When merging binary clauses, we can simply produce the LRAT chain by (1) using the two binary
  // clauses and (2) the reason clause from the literals to the representatives.
  //
  // The same approach does not work for merging gates because the representative might be also a
  // representative of another literal (because of eager rewriting), requiring to resolve more than
  // once on the same literal. An example of this are the two gates 4=-2&7 and 6=-2&1, the rewriting
  // 7=1 and the equivalence 4=1. The simple road of merging 6 and 4 (requires resolving away 1) +
  // adding the rewrite 4 to 1 (requires adding 1) does not work.
  //
  // Therefore, we actually go for the more regular road and produce two
  // equivalence: the merge from the LHS, followed by the actual equivalence (by combining it with
  // the rewrite).  In DRAT this is less important because the checker finds a chain and is less
  // restricted than our LRAT chain.
  bool merge_literals_equivalence (int lit, int other, Clause *c1, Clause *c2);
  bool merge_literals_lrat (Gate *g, Gate *h, int lit, int other, const std::vector<uint64_t>& = {}, const std::vector<uint64_t> & = {});
  bool merge_literals (int lit, int other, bool learn_clauses = true);

  // proof production
  vector<LitClausePair> lrat_chain;
  void push_lrat_id (const Clause *const c, int lit);
  void push_lrat_unit (int lit);

  // pushes the clause with the reasons to rewrite clause
  // unless:
  //   - the rewriting is not necessary (resolvent_marked == 1)
  //   - it is overwritten by one of the arguments
  void push_id_and_rewriting_lrat_unit (Clause *c, Rewrite rewrite1,
				   std::vector<uint64_t> &chain, bool = true,
				   Rewrite rewrite2 = Rewrite (),
				   int execept_lhs = 0, int except_lhs2 = 0);
  void push_id_and_rewriting_lrat (Clause *c, Rewrite rewrite1,
				   std::vector<uint64_t> &chain, bool = true,
				   Rewrite rewrite2 = Rewrite (),
				   int execept_lhs = 0, int except_lhs2 = 0);
  void push_id_and_rewriting_lrat_full (Clause *c, Rewrite rewrite1,
				   std::vector<uint64_t> &chain, bool = true,
				   Rewrite rewrite2 = Rewrite (),
					int execept_lhs = 0, int except_lhs2 = 0);
  // TODO: does nothing except pushing on the stack, remove!
  void push_id_and_rewriting_lrat (const std::vector<LitClausePair> &c, Rewrite rewrite1,
				   std::vector<uint64_t> &chain, bool = true,
				   Rewrite rewrite2 = Rewrite (),
				   int execept_lhs = 0, int except_lhs2 = 0);
  void produce_lrat_for_rewrite (std::vector<uint64_t> &chain, Rewrite rewrite, int);
  void unmark_marked_lrat ();
  void unmark_lrat_resolvents ();
  void mark_lrat_resolvents (int lit, int src = 0, int dst = 0, int except = 0, int except2 = 0);
  void mark_lrat_resolvents (Clause *, int src = 0, int dst = 0, int except = 0, int except2 = 0);
  void mark_lrat_resolvents (std::vector<LitClausePair> &c, int src = 0, int dst = 0, int except = 0, int except2 = 0);
  void update_and_gate_build_lrat_chain (Gate *g, Gate *h, int src, uint64_t id1, uint64_t id2, int dst,
					 std::vector<uint64_t> & extra_reasons_lit, std::vector<uint64_t> &extra_reasons_ulit);
  void update_and_gate_unit_build_lrat_chain (Gate *g, int src, uint64_t id1, uint64_t id2, int dst,
      std::vector<uint64_t> &extra_reasons_lit,
      std::vector<uint64_t> &extra_reasons_ulit);
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
  void update_and_gate (Gate *g, GatesTable::iterator, int src, int dst, uint64_t id1, uint64_t id2, int falsified = 0, int clashing = 0);
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

  Gate* find_and_lits (const vector<int> &rhs, Gate *except = nullptr);
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

  void merge_condeq (int cond, lit_equivalences &condeq, lit_equivalences &not_condeq);
  void
  find_conditional_equivalences (int lit,
                                 lit_implications &condbin,
                                 lit_equivalences &condeq);
  void
  copy_conditional_equivalences (int lit, lit_implications &condbin);
  void check_ite_implied (int lhs, int cond, int then_lit, int else_lit);
  void check_ite_gate_implied (Gate *g);
  void check_and_gate_implied (Gate *g);
  void delete_proof_chain ();

  // ite gate extraction
  void extract_ite_gates_of_literal (int);
  void extract_ite_gates_of_variable (int idx);
  void extract_condeq_pairs (int lit, lit_implications &condbin, lit_equivalences &condeq);
  void init_ite_gate_extraction (std::vector<Clause *> &candidates);
  lit_implications::const_iterator find_lit_implication_second_literal (int lit, lit_implications::const_iterator begin,
                                    lit_implications::const_iterator end);
  void search_condeq (int lit, int pos_lit,
                             lit_implications::const_iterator pos_begin,
                             lit_implications::const_iterator pos_end, int neg_lit,
                             lit_implications::const_iterator neg_begin,
                             lit_implications::const_iterator neg_end,
                             lit_equivalences &condeq);
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
  void learn_congruence_unit_falsifies_lrat_chain (Gate *g, int src, int dst, uint64_t id1, uint64_t id2, int clashing, int falsified, int unit);
  void learn_congruence_unit_unit_lrat_chain (Gate *g, int unit); 
  void learn_congruence_unit_when_lhs_set (Gate *g, int src, uint64_t id1, uint64_t id2, int dst);

  void find_units();
  void find_equivalences();
  void subsume_clause (Clause *subsuming, Clause *subsumed);
  bool find_subsuming_clause (Clause *c);
  void produce_rewritten_clause_lrat_and_clean (vector<LitClausePair>&, Rewrite rew1,
					 Rewrite rew2,
				   int execept_lhs = 0, int except_lhs2 = 0);
  Clause* produce_rewritten_clause_lrat (Clause *c, Rewrite rew1,
					 Rewrite rew2,
				   int execept_lhs = 0, int except_lhs2 = 0);
  Clause* produce_rewritten_clause_lrat (Clause *c, int except = 0, uint64_t id1 = 0, uint64_t id2 = 0,
				   int except_other = 0, uint64_t id_other1 = 0, uint64_t id_other2 = 0,
				   int execept_lhs = 0, int except_lhs2 = 0);
  // binary extraction and ternary strengthening
  void extract_binaries ();
  bool find_binary (int, int) const;

  Clause *new_clause ();
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

  signed char& proof_marked (int lit);
  signed char& resolvent_marked (int lit);
  
  // negbincount (lit) -> noccs (-lit)

};

} // namespace CaDiCaL

#endif