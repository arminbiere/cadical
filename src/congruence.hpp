#ifndef _congruenc_hpp_INCLUDED
#define _congruenc_hpp_INCLUDED

#include <algorithm>
#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <queue>
#include <string>
#include <sys/types.h>
#include <vector>

#include "clause.hpp"
#include "hash.hpp"
#include "util.hpp"

namespace CaDiCaL {

typedef int64_t LRAT_ID;

// This implements the clausal congruence algorithm from Biere at
// al. [SAT 2024]. We refer to the paper for details, but in
// essence, the idea is to detect gate definitions in the set of
// clauses.
//
// The algorithm works by detecting equivalences and rewriting them in the
// gates (not in the clauses that defines them yet! this is done later in
// decompose).
//
// In Step 0, we do simplification over the binary and ternary clauses. This
// is actually more aggressive and a subset of what decompose and ternary.
//
// In Step 1, we detect all gates in the input clauses.
//
// In Step 2, we start the replacement. the rewriting is done eagerly over
// the equivalences rewritten so far, not over the equivalence detected.
// This is probably not necessary but makes detecting gates faster than if
// we would eagerly rewrite everything. After each rewriting:
//
// - we detect if the gate was already present. If it was, we can merge both
// LHS of the gates.
//
// - we simplify the gates, leading to potentially units.
//
// This rewriting of everything so far is done 'eagerly', while the set of
// all detected equivalences is the 'lazy' part of the algorithm. Each
// rewriting in the 'lazy' part is slowly imported in the 'eager' part. We
// favor simplifying gates over rewriting, but do not interrupt a rewriting
// round. Therefore, we still have to handle the detection of units during
// rewriting.
//
// We do not try to detect new gates, we only convert ITE gates to AND gates
// or XOR gates after rewriting or simplifications.
//
// The rewritings are done to the normal form according to the lazy
// normalization. This is an important point for performance.
//
// Step 3: Finally, after rewriting everything, we can forward subsume the
// clauses, but we let the full rewriting and the replacement be done by
// decompose.
//
// In CaDiCaL we have ported the entire algorithm to LRAT, which was not
// supported in Kissat. This actually forced us to detect more cases of
// units and special cases that Kissat misses, because it often made the
// proofs easier to generate (fewer special cases of units or duplicated
// literals).
//
// While the idea is generally easy, it is extremely complicated to do in
// practise and getting to the last cases is an absolutely horrible
// experience. There is at least one corner case in the cade that we only
// managed to reach after fuzzing (optimized) after nearly one week of
// fuzzing over a 64 core machine (not including the 32 + 24 cores that we
// used sporadically and did not hit those cases either).
//
// Because of LRAT we changed some things compared to Kissat: the algorithm
// relies on a union-find datastructure. In Kissat there is no path
// compression. Here, we do actually compress paths but only if we generated
// the binary clauses corresponding to that equivalence. This compression
// did improve performance according to Armin and was not considered
// important in Kissat.
//
// We have two structures for merging:
//   - the lazy ones contains alls merges, with functions like
//   find_representative
//
//   - the eager version that gets the merges one by one, with functions
//   like find_eager_representatives
//
// The two structures are nicely separated and we only working on one of
// them except for:
//
//    1. When propagating one equivalence, we first important the
//    equivalence from the lazy to the eager version, producing the full
//    chain.
//
//    2. When merging the literals, we merge the literals given by the lazy
//    structure, then we merge their representative in the eager version,
//    updating only the lazy structure. We do not update the eager version.
//
// We experimented with the hash function and found that it has a huge
// impact on performance (don't forget to take the gate type into
// consideration!). We decided to use the default std::hash and played with
// the number of buckets, but did not see much difference.
//
// Actually we add one more step compared to Kissat: we consider the binary
// clauses as a gate return false and merge those gates with existing gates.
// It does not happen very often, but actually it happens on some problems
// several times. If we set any literal, we actually restart the loop and
// try to merge more variables.
//
// There is another (subtle) difference to Kissat: we keep track of
// degenerated gates even in non-production mode. It is not clear to us how
// useful this really is, but it is this make the procedure more complete,
// because it is more likely to trigger the special cases that we have added
// to CaDiCaL to propagate units.
//
// For the LRAT production, we rely on the internal proof producing
// capabilities with the variable `lrat_chain` that contains the IDs of the
// clauses required.
//
// Remark (*)
//
// One more vexing thing: we cannot eagerly remove units anymore when
// producing LRAT with lazy rewriting on the clauses. It very very rarely
// breaks, but down the road we would need to distinguish between literals
// that have been removed from the gate and literals that appear in the gate
// and have not been simplified yet. After much thinking, we dediced (in the
// case a unit is found) to rewrite the gate clause. It is annoying, but
// rewriting the units seems more important to find units and merge literals
// early. This concerns only literals removed as a side-effect of rewriting,
// not the literals removed during simplification.
//

struct Internal;

// Here come some implementation remarks.
//
// An important point: We cannot use internal->lrat_chain and
// internal->clause because in most places we can interrupt the
// transformation to learn a new clause representing an equivalence.
// However, we can only have 2 layers so we use this->lrat_chain and
// internal->lrat_chain when we really produce the proof.
//
// One of the tricky things throughout the proofs is that the LHS is *not*
// rewritten ever (except below). This means that the normalization need to
// ignore the LHS of gates during normalization. We might also ignore two
// literals (like in XOR gates during merges). Be careful with this, it is
// really really hard to trigger bugs if you ignore the wrong literal. They
// do happen, but it is rather rare (consider that an entire week-end with
// 24 cores will not find all of those issues).
//
// As mentioned above, the LHS is most of the time kept as is. This is
// however not true for degenerated gates: We tried to mirror that feature
// but failed because it is too hard to keep track of the resulting status
// of the gate (degenerated gate might seem normal again after rewriting on
// the LHS). Therefore, we actually also rewrite the LHS in those (rare)
// cases.
//
// Another subtle point is the handling of units (for example in binary
// clauses or when deriving units). In Kissat this is done directly. For
// example, when adding a binary clauses, there is a direct check if one
// literal is already set leading to a unit. This is nice for DRAT proofs
// but highly impractible for LRAT where the regularity is critical to be
// able to produce correct proofs.
//
// For AND gates, we ensure that the other_neg_lhs_id () is *never* empty,
// unless LRAT is off. This was not the case at the beginning of the
// implementation, but it really makes the implementation more easy.

// Maximum arity to be able to use bits to keep information. Superseeds the
// options.
#define LD_MAX_ARITY 26
#define MAX_ARITY ((1 << LD_MAX_ARITY) - 1)

/*------------------------------------------------------------------------*/
// Tags to indentify the kind of gates.
enum class Gate_Type : int8_t { And_Gate, XOr_Gate, ITE_Gate };
std::string string_of_gate (Gate_Type t);

/*------------------------------------------------------------------------*/
// Wrapper when we are looking for implication in if-then-else gates. This
// is done in two steps: finding implications, then finding equivalences.
// Both of them are conditional, but the condition is only in the context
// not in the structure. Without LRAT we would not need to remember the
// gate.
struct lit_implication {
  int first;
  int second;
  Clause *clause;
  lit_implication (int f, int s, Clause *_id)
      : first (f), second (s), clause (_id) {}
  lit_implication (int f, int s) : first (f), second (s), clause (0) {}
  lit_implication () : first (0), second (0), clause (nullptr) {}
  void swap () { std::swap (first, second); }
};

// Wrapper when we are looking for equivalence for if-then-else-gate. They
// are produced by merging implication. We have to keep the clauses for the
// lrat reasons.
struct lit_equivalence {
  int first;
  int second;
  Clause *first_clause;
  Clause *second_clause;
  void check_invariant () const {
    assert (second_clause);
    assert (first_clause);
    assert (std::find (begin (*first_clause), end (*first_clause), first) !=
            end (*first_clause));
    assert (std::find (begin (*second_clause), end (*second_clause),
                       second) != end (*second_clause));
    assert (std::find (begin (*first_clause), end (*first_clause),
                       -second) != end (*first_clause));
    assert (std::find (begin (*second_clause), end (*second_clause),
                       -first) != end (*second_clause));
  }
  lit_equivalence (int f, Clause *f_id, int s, Clause *s_id)
      : first (f), second (s), first_clause (f_id), second_clause (s_id) {}
  lit_equivalence (int f, int s)
      : first (f), second (s), first_clause (nullptr),
        second_clause (nullptr) {}
  lit_equivalence ()
      : first (0), second (0), first_clause (nullptr),
        second_clause (nullptr) {}
  // swaps the first and the second literal (and their corresponding id)
  lit_equivalence swap () {
    std::swap (first, second);
    std::swap (first_clause, second_clause);
    return *this;
  }
  // negate both literals
  lit_equivalence negate_both () {
    first = -first;
    second = -second;
    std::swap (first_clause, second_clause);
    return *this;
  }
};

typedef std::vector<lit_implication> lit_implications;
typedef std::vector<lit_equivalence> lit_equivalences;

/*------------------------------------------------------------------------*/
// Main structure for our LRAT proofs: a literal (or a number for XOR gates)
// and the corresponding clause.
struct LitClausePair {
  int current_lit; // current literal from the gate
  Clause *clause;
  LitClausePair (int lit, Clause *cl) : current_lit (lit), clause (cl) {}
  LitClausePair () : current_lit (0), clause (nullptr) {}
};

/*------------------------------------------------------------------------*/
// Used for XOR gate detection, synonym of std::pair<int,LRAT_ID>.
struct LitIdPair {
  int lit; // current literal from the gate
  LRAT_ID id;
  LitIdPair (int l, LRAT_ID i) : lit (l), id (i) {}
  LitIdPair () : lit (0), id (0) {}
};

/*------------------------------------------------------------------------*/

// Sorting the scheduled clauses is way faster if we compute and save the
// clause size in the schedule to avoid pointer access to clauses during
// sorting.  This doubles the schedule size though.

struct ClauseSize {
  size_t size;
  Clause *clause;
  ClauseSize (int s, Clause *c) : size (s), clause (c) {}
  ClauseSize (Clause *c) : size (c->size ()), clause (c) {}
  ClauseSize () {}
};

struct smaller_clause_size_rank {
  typedef size_t Type;
  Type operator() (const ClauseSize &a) { return a.size; }
};

/*------------------------------------------------------------------------*/
// For LRAT, we want to remember if the gate is not normal, namely that it
// does not have the normal number of clauses.
//
// We make the enumeration over integers to make it easier to combine values
// togethen.
//
// There are many special cases for ITE gates and we have to keep track of
// them as it is a gate property (rewriting might not make it obvious
// anymore).
// a = (a ? t : e) results in no -t and no +e gate (a --> a = t  == (-a v -a
// v t) & (-a v a v -t)) a = (-a ? t : e) results in no +t and no -e gate a
// = (c ? a : e) results in no t gate (none of them) a = (c ? t : a) results
// in no e gate (none of them)
//
// We also use it for AND gates:
// a = (a & b)
// false = (a & b)
//
// The latter version can only happen when converting ITE gates to AND
// gates.
//
// They have a peculiarity: being special can fix itself (according to the
// literals in the gate), but it won't make the missing reason clauses
// appear. To avoid one more special case, we rewrite the LHS in that case
// too to make sure it remains special.
//
enum Special_Gate {
  NORMAL = 0,
  NO_PLUS_THEN = (1 << 0),
  NO_NEG_THEN = (1 << 1),
  NO_THEN = NO_PLUS_THEN + NO_NEG_THEN,
  NO_PLUS_ELSE = (1 << 2),
  NO_NEG_ELSE = (1 << 3),
  DEGENERATED_AND = (1 << 4),           // a = (a & b)
  DEGENERATED_AND_LHS_FALSE = (1 << 5), // false = (a & b)
  NO_ELSE = NO_PLUS_ELSE + NO_NEG_ELSE,
  COND_LHS = NO_NEG_THEN + NO_PLUS_ELSE,
  UCOND_LHS = NO_PLUS_THEN + NO_NEG_ELSE,
};

std::string special_gate_str (int8_t f);

inline bool ite_flags_no_then_clauses (int8_t flag) {
  return (flag & NO_THEN) == NO_THEN;
}

inline bool ite_flags_no_else_clauses (int8_t flag) {
  return (flag & NO_ELSE) == NO_ELSE;
}

inline bool ite_flags_neg_cond_lhs (int8_t flag) {
  return (flag & UCOND_LHS) == UCOND_LHS;
}

inline bool ite_flags_cond_lhs (int8_t flag) {
  return (flag & COND_LHS) == COND_LHS;
}

/*------------------------------------------------------------------------*/
// We need an std::option for optional LRAT reasons. We initially used
// std::optional, but std::optional is C++17 sadly, so we used an
// alternative. Actually, std::optional has bad performance under some
// systems.
struct my_dummy_optional {
  LitClausePair content;
  my_dummy_optional () : content (0, 0) {}
  bool operator() () const { return content.current_lit; }
  my_dummy_optional operator= (LitClausePair p) {
    content = p;
    return *this;
  }
  void reset () { content = LitClausePair (0, 0); }
};

/*------------------------------------------------------------------------*/

// The core structure of this algorithm: the gate. It is composed of a
// left-hand side and an array of right-hand side.
//
// There are a few tags to help remembering the status of the gate (like
// deleted)
//
// To keep track of the proof we use two extra arrays:
//  - `neg_lhs_ids' contains the long clause for AND gates. Otherwise, it is
//  empty.
//  - `pos_lhs_ids' contains all the remaining gates.
//
// We keep the reasons with an index. This index depends on the gates:
//
//   - AND-Gates and ITE-Gates: the index is the literal from the RHS
//
//   - XOR-Gates: if you order the clauses by the order of the literals,
//   each literal is either positive (bit '1') or negative (bit '0'). This
//   gives a number that we can use.
//
//
// Important for the proofs: the LHS is not eagerly updated. Therefore, in
// most functions for rewriting, there is a parameter to ignore the
// literals.
//
// One warning for degenerated gate: it is a monotone property on the
// defining clauses, but not on the LHS/RHS as the LHS is not rewritten:
// take 4 = AND 3 4 (degenerated with only the clause -4 3) with a rewriting
// 4 -> 1 (unchanged clause) and later 1 -> 3 (unchanged clause) but you do
// not know anymore from the gate that it is degenerated
//
// We use flexible array members, which are actually only a C feature,
// although most compilers support it. Unlike clauses, we have C++ class
// within the struct for LRAT proofs. Therefore, we actually need a proper
// constructor/destructor.
//
// Note from Mathias: I did not believe that FMA would help, but there are
// problems with several dozen GB of memory. And for those instances, the
// improvements are very important more than 10%.
//
// We initially had the vector for lrat as part of the structure. As the
// memory usage is extremely high we tried to get rid of it and we observed
// a memory reduction of 2GB on `hash_table_find_safety_size_29.cnf.xz` by
// using a pointer to something that is not initialized.
//
// Now also the merging in LRAT preoduces many many useless (because
// transitive) binary clauses. We don't really want to add theses clauses to
// keep the behavior similar between LRAT and non-LRAT. Therefore, we add
// those clauses as temporary and do not add them to the glocal set of
// clauses (unless those are needed).
//
// However, even if most of the binary clauses are subsumed, we need to keep
// enough of them. Therefore, we actually promote some from redundant to
// irredundant in the binary clause handling. Kissat does not need this
// code, because all binary irredundant.
struct Gate {
#ifdef LOGGING
  uint64_t raw_id;
#endif
  struct LRAT_Reasons {
    vector<LitClausePair> pos_lhs_ids;
    my_dummy_optional neg_lhs_id;
  } *lrat_reasons;
  int lhs;
  Gate_Type tag;
  bool garbage : 1;
  bool indexed : 1;
  bool marked : 1;
  bool with_id : 1;
  int8_t degenerated_gate = Special_Gate::NORMAL;
  int size;
#ifndef NFLEXIBLE
  int rhs[];
#else
  int rhs[2];
#endif
  int arity () const { return size; }
#ifdef LOGGING
  uint64_t &id () {assert (with_id); return raw_id;};
  uint64_t id () const {if (with_id) return raw_id; else return 0;};
#endif
  bool has_reasons () {
    return with_id && lrat_reasons;
  }

  bool operator== (Gate const &lhs) {
    if (tag != lhs.tag)
      return false;
    if (size != lhs.size)
      return false;
    for (int i = 0; i < size; ++i)
      if (rhs[i] != lhs.rhs[i])
        return false;
    return true;
  }
  // default constructor
  Gate ()
      : lrat_reasons (nullptr), lhs (0), garbage (false), indexed (false),
        marked (false), size (0) {}
  Gate (int _size)
      : lrat_reasons (nullptr), lhs (0), tag (Gate_Type::And_Gate),
        garbage (false), indexed (false), marked (false), size (_size) {
    assert (size >= 2);
  }

  static size_t raw_bytes (int size) {
    assert (size > 1);
    const size_t header_bytes = sizeof (Gate);
    const size_t actual_literal_bytes = size * sizeof (int);
    size_t combined_bytes = header_bytes + actual_literal_bytes;
#ifdef NFLEXIBLE
    const size_t faked_literals_bytes = sizeof ((Gate *) 0)->rhs;
    combined_bytes -= faked_literals_bytes;
#endif
    size_t aligned_bytes = align (combined_bytes, 8);
    return aligned_bytes;
  }
  static size_t bytes_to_allocate (int size, bool with_id) { return raw_bytes (size) - (with_id ? 0 : offset ()); }
  static size_t offset () {
#ifndef LOGGING
    return sizeof (LRAT_Reasons*);
#else
    return sizeof (uint64_t) + sizeof (LRAT_Reasons*);
#endif
  }

  // creation of a gate with either the size or of the right-hand side
  static Gate *new_gate (size_t n, bool lrat);
  static Gate *new_gate (const std::vector<int> &v, bool lrat);
  static Gate *new_gate (const_literal_iterator begin,
                         const_literal_iterator end, bool lrat);

  // deletion of a gate
  static void delete_gate (Gate *&g);

  literal_iterator begin () { return rhs; }
  literal_iterator end () { return rhs + size; }

  const_literal_iterator begin () const { return rhs; }
  const_literal_iterator end () const { return rhs + size; }

  // reduce the size of the rhs of the gate
  void resize (int n);
  // set the rhs to the vector passed as argument
  void set (const std::vector<int> &new_rhs);
  // set the rhs based on the iterators passed as argument
  void set (const_literal_iterator begin, const_literal_iterator end);

  vector<LitClausePair> &pos_lhs_ids () {
    assert (lrat_reasons);
    return lrat_reasons->pos_lhs_ids;
  }
  my_dummy_optional &neg_lhs_id () {
    assert (lrat_reasons);
    return lrat_reasons->neg_lhs_id;
  }
  const vector<LitClausePair> &pos_lhs_ids () const {
    assert (lrat_reasons);
    return lrat_reasons->pos_lhs_ids;
  }
  const my_dummy_optional &neg_lhs_id () const {
    assert (lrat_reasons);
    return lrat_reasons->neg_lhs_id;
  }
};

typedef vector<Gate *> Gate_Occurrence;
typedef vector<Gate_Occurrence> Gate_Occurrences;

// Equality on gate inputs assuming that the literals are normalized in the
// same way.
struct GateEqualTo {
  bool operator() (const Gate *const lhs, const Gate *const rhs) const {
    if (lhs->tag != rhs->tag)
      return false;
    if (lhs->arity () != rhs->arity ())
      return false;
    for (int i = 0; i < rhs->arity (); ++i) {
      if (lhs->rhs[i] != rhs->rhs[i])
        return false;
    }
    return true;
  }
};

struct Hash {
  Hash (std::array<uint64_t, 16> &ncs) : nonces (ncs) {}
  const std::array<uint64_t, 16> &nonces;
  inline size_t operator() (const Gate *const g) const;
};

/*------------------------------------------------------------------------*/
// Useful for LRAT generation to update the clauses in a controlled way,
// pontentially overwriting the eager rewriting..
struct Rewrite {
  int src, dst;
  LRAT_ID id1;
  LRAT_ID id2;

  Rewrite (int _src, int _dst, LRAT_ID _id1, LRAT_ID _id2)
      : src (_src), dst (_dst), id1 (_id1), id2 (_id2) {}
  Rewrite () : src (0), dst (0), id1 (0), id2 (0) {}
};

/*------------------------------------------------------------------------*/
// This is a more compact representation of binary clauses. Sadly we have to
// include the IDs in the clause making it larger than necessary. We also
// need to include the clause pointer in order to be able to delete the
// subsumed clause.
struct CompactBinary {
  Clause *clause;
  LRAT_ID id;
  int lit1, lit2;
  CompactBinary (Clause *c, LRAT_ID i, int l1, int l2)
      : clause (c), id (i), lit1 (l1), lit2 (l2) {
    assert (!c || c->size () == 2);
    assert (!c || c->literals[0] == lit1 || c->literals[1] == lit1);
    assert (!c || c->literals[0] == lit2 || c->literals[1] == lit2);
  }

  CompactBinary () : clause (nullptr), id (0), lit1 (0), lit2 (0) {}
};

/*------------------------------------------------------------------------*/

struct Closure {

  Closure (Internal *i);
  ~Closure ();
  Gate *dummy_search_gate = nullptr;
  int dummy_search_gate_capacity = 0;

  Internal *const internal;
  vector<Clause *> extra_clauses;
  vector<CompactBinary> binaries;
  std::vector<std::pair<size_t, size_t>> offsetsize;
  bool full_watching = false;
  std::array<uint64_t, 16> nonces; // for better hashing
  typedef hash<Gate *, Hash, GateEqualTo, std::equal_to<Gate *>> GatesTable;

  vector<signed char> marks; // marking structure
  // remember the ids and the literal. 2 and 4 are
  // only used for lrat proofs, but we need 1 to
  // promote binary clauses to irredundant
  vector<LitClausePair> mu1_ids, mu2_ids, mu4_ids;

  vector<int> lits;         // result of definitions
  vector<int> rhs;          // stack for storing RHS
  vector<int> unsimplified; // stack for storing unsimplified version (XOR,
                            // ITEs) for DRAT proof
  vector<int> chain;  // store clauses to be able to delete them properly
  vector<int> clause; // storing partial clauses
  vector<uint64_t>
      glargecounts; // count for large clauses to complement internal->noccs
  vector<uint64_t> gnew_largecounts; // count for large clauses to
                                     // complement internal->noccs
  GatesTable table;

  // temporary variable for ITE gate extraction: condbin for condition
  // implication and condeq for the equivalences.
  std::array<lit_implications, 2> condbin;
  std::array<lit_equivalences, 2> condeq;

  // schedule of literals to rewrite and marking structure to check if
  // already scheduled
  queue<int> schedule;
  vector<bool> scheduled;

  std::vector<Clause *> new_unwatched_binary_clauses; // TODO: unused
  // LRAT proofs
  vector<int> resolvent_analyzed;
  mutable vector<LRAT_ID> lrat_chain; // storing LRAT chain

#ifdef LOGGING
  uint64_t fresh_id;
#endif

  uint64_t &new_largecounts (int lit);
  uint64_t &largecounts (int lit);

  void unmark_all ();
  vector<int> representant;              // union-find
  vector<int> eager_representant;        // union-find
  vector<LRAT_ID> representant_id;       // lrat version of union-find
  vector<LRAT_ID> eager_representant_id; // lrat version of union-find
  // next literal in our union-find structure
  int &representative (int lit);
  // next literal in our union-find structure
  int representative (int lit) const;
  // clause id justifying the rewriting to the next literal in our
  // union-find structure
  LRAT_ID &representative_id (int lit);
  // clause id justifying the rewriting to the next literal in our
  // union-find structure
  LRAT_ID representative_id (int lit) const;
  // next literal in our eager union-find structure
  int &eager_representative (int lit);
  // next literal in our eager union-find structure
  int eager_representative (int lit) const;
  // clause id justifying the rewriting to the next literal in our eager
  // union-find structure
  LRAT_ID &eager_representative_id (int lit);
  // clause id justifying the rewriting to the next literal in our eager
  // union-find structure
  LRAT_ID eager_representative_id (int lit) const;
  std::vector<char> lazy_propagated_idx;
  size_t units; // next trail position to propagate
  // checks whether a literal has been already eager propagated (and
  // therefore can be removed from the clauses)
  char &lazy_propagated (int lit);

  // representative in the union-find structure in the lazy equivalences
  int find_representative (int lit);
  // representative in the union-find structure in the lazy equivalences.
  // only useful if you do not care about proofs like during forward
  // subsumption.
  int find_representative_and_compress_no_proofs (int lit);
  // returns the representant assumping that path compression has already
  // been implied.
  //
  // This is mostly useful at the end in the forward subsumption, where no
  // new rewriting is happening.
  int find_representative_already_compressed (int lit);
  // find the representative and produce the binary clause representing the
  // normalization from the literal to the result.
  int find_representative_and_compress (int, bool update_eager = true);
  // find the lazy representative for the `lit' and `-lit'
  void find_representative_and_compress_both (int);
  // find the eager representative
  int find_eager_representative (int);

  // compreses the path from lit to the representative with a new clause if
  // needed. Save internal->lrat_chain to avoid any issue.
  int find_eager_representative_and_compress (int);
  // Import the path from the literal and its negation to the representative
  // in the lazy graph to the eager part, producing the binary clauses.
  void import_lazy_and_find_eager_representative_and_compress_both (int);

  // returns the ID of the LRAT clause for the normalization from the
  // literal lit to its argument, assuming that the representative was
  // already compressed.
  LRAT_ID find_representative_lrat (int lit);
  // returns the ID of the LRAT clause for the eager normalization from the
  // literal lit to its argument assuming that the representative was
  // already compressed.
  LRAT_ID find_eager_representative_lrat (int lit);

  // Writes the LRAT chain required for the eager normalization to
  // `lrat_chain`.
  void produce_eager_representative_lrat (int lit);
  // Writes the LRAT chain required for the lazy normalization to
  // `lrat_chain`.
  void produce_representative_lrat (int lit);

  // promotes a clause from redundant to irredundant. We do this for all
  // clauses involved in gates to make sure that we produce correct result.
  void promote_clause (Clause *);

  // Merge functions. We actually need different several versions for LRAT
  // in order to simplify the proof production. We distinguish between the
  // functions that the clauses as argumunts and the functions that takes
  // the LRAT chains as argument. The latter will learn additional clauses,
  // while the former already knows those additional clauses and only has to
  // merge the representants.
  //
  // When merging binary clauses, we can simply produce the LRAT chain by
  // (1) using the two binary clauses and (2) the reason clause from the
  // literals to the representatives.
  //
  // The same approach does not work for merging gates because the
  // representative might be also a representative of another literal
  // (because of eager rewriting), requiring to resolve more than once on
  // the same literal. An example of this are the two gates 4=-2&7 and
  // 6=-2&1, the rewriting 7=1 and the equivalence 4=1. The simple road of
  // merging 6 and 4 (requires resolving away 1) + adding the rewrite 4 to 1
  // (requires adding 1) does not work.
  //
  // Therefore, we actually go for the more regular road and produce two
  // equivalence: the merge from the LHS, followed by the actual equivalence
  // (by combining it with the rewrite).  In DRAT this is less important
  // because the checker finds a chain and is less restricted than our LRAT
  // chain.

  // Merges the two literals based on the clauses, assuming that c1 and c2
  // are the two clauses and assuming the two literals have not been set
  // (because propagation can be done exaustively on binary clauses, so
  // either both already have a value or none).
  bool merge_literals_from_clauses (int lit, int other, Clause *c1,
                                    Clause *c2);
  bool merge_literals (Gate *g, Gate *h, int lit, int other,
                       const std::vector<LRAT_ID> & = {},
                       const std::vector<LRAT_ID> & = {});
  bool merge_literals (int lit, int other,
                       const std::vector<LRAT_ID> & = {},
                       const std::vector<LRAT_ID> & = {});
  // factoring out the merge w.r.t. both cases above
  bool really_merge_literals (int lit, int other, int repr_lit,
                              int repr_other,
                              const std::vector<LRAT_ID> & = {},
                              const std::vector<LRAT_ID> & = {});

  // proof production
  vector<LitClausePair> lrat_chain_and_gate;
  // pushed the id of the reason of literal lit to the lrat chain
  void push_lrat_unit (int lit);

  // This functions produces the LRAT reasoning to normalize the clause.
  //
  // It pushes the clause with the reasons to rewrite clause unless: -
  // the rewriting is not necessary (resolvent_marked == 1) - it is
  // overwritten by one of the arguments
  //
  // This does not produce a new clause and only extends the chain. It also
  // checks that no reason for rewriting is added twice.
  void produce_lrat_chain_for_rewriting (Clause *c, Rewrite rewrite1,
                                         std::vector<LRAT_ID> &chain,
                                         bool = true,
                                         Rewrite rewrite2 = Rewrite (),
                                         int execept_lhs = 0,
                                         int except_lhs2 = 0);
  // push the id of c to the lrat chain.
  void push_id_on_chain (std::vector<LRAT_ID> &chain, Clause *c);
  // push the ids of c to the lrat chain in order.
  void push_id_on_chain (std::vector<LRAT_ID> &chain,
                         const std::vector<LitClausePair> &c);
  void push_id_on_chain (std::vector<LRAT_ID> &chain,
                         const my_dummy_optional &c);
  // Push the id required to rewrite lit to chain according to the rewrite.
  void push_id_on_chain (std::vector<LRAT_ID> &chain, Rewrite rewrite,
                         int lit);

  // produces the LRAT for merging two AND-gates, including all the special
  // cases.
  void produce_lrat_for_and_merge (Gate *g, Gate *h,
                                   std::vector<LRAT_ID> &extra_reasons_lit,
                                   std::vector<LRAT_ID> &extra_reasons_ulit,
                                   bool remove_units = true);
  void update_and_gate_unit_build_lrat_chain (
      Gate *g, int src, LRAT_ID id1, LRAT_ID id2, int dst,
      std::vector<LRAT_ID> &extra_reasons_lit,
      std::vector<LRAT_ID> &extra_reasons_ulit);
  // occs
  Gate_Occurrences gatetab;
  Gate_Occurrence &goccs (int lit);
  void connect_goccs (Gate *g, int lit);
  vector<Gate *> garbage;
  // mark the gate garbage and add it to the list of garbage clauses
  void mark_garbage (Gate *);
  // remove the gate from the hash table
  bool remove_gate (Gate *);
  // remove the gate given by the iterator from the hash table
  bool remove_gate (GatesTable::iterator git);
  // adds the gate from the hash table
  void index_gate (Gate *);

  // second counter for size, complements noccs
  uint64_t &largecount (int lit);

  /*------------------------------------------------------------------------*/
  // simplification
  bool skip_and_gate (Gate *g);
  bool skip_xor_gate (Gate *g);
  void update_and_gate (Gate *g, GatesTable::iterator, int src, int dst,
                        LRAT_ID id1, LRAT_ID id2, int falsified = 0,
                        int clashing = 0);
  void update_xor_gate (Gate *g, GatesTable::iterator);
  void shrink_and_gate (Gate *g, int falsified = 0, int clashing = 0);
  bool simplify_gate (Gate *g);
  void simplify_and_gate (Gate *g);
  void simplify_ite_gate (Gate *g);
  Clause *simplify_xor_clause (int lhs, Clause *);
  void simplify_xor_gate (Gate *g);
  bool simplify_gates (int lit);
  void simplify_and_sort_xor_lrat_clauses (const vector<LitClausePair> &,
                                           vector<LitClausePair> &, int,
                                           int except2 = 0, bool flip = 0);
  void simplify_unit_xor_lrat_clauses (const vector<LitClausePair> &, int);

  // rewriting
  bool rewriting_lhs (Gate *g, int dst);
  bool rewrite_gates (int dst, int src, LRAT_ID id1, LRAT_ID id2);
  bool rewrite_gate (Gate *g, int dst, int src, LRAT_ID id1, LRAT_ID id2);
  void rewrite_xor_gate (Gate *g, int dst, int src);
  void rewrite_and_gate (Gate *g, int dst, int src, LRAT_ID id1,
                         LRAT_ID id2);
  void rewrite_ite_gate (Gate *g, int dst, int src);

  /*------------------------------------------------------------------------*/

  bool propagate_unit (int lit);
  bool propagate_units ();
  size_t propagate_units_and_equivalences ();

  // propagate the first found equivalence to all gates by rewriting through
  // all gates..
  bool propagate_equivalence (int lit);

  // overall scheduling
  void init_closure ();
  void reset_closure ();
  void reset_extraction ();
  void reset_and_gate_extraction ();
  void extract_gates ();
  void extract_congruence ();
  void find_units ();
  void find_equivalences ();
  // Use the binary clauses as and-gates returning false. We do not want to
  // stress the hash-table by adding all of them (nor actually introducing a
  // false literal), but there are problems with this really happens often.
  bool propagate_binary_clauses_in_and_gates ();

  /*------------------------------------------------------------------------*/
  // searching gates or creating new ones if gate was not found
  Gate *find_gate_lits (const_literal_iterator begin,
                        const_literal_iterator end, Gate_Type typ,
                        Gate *except = nullptr);
  Gate *find_gate_lits (const std::vector<int> &rhs, Gate_Type typ,
                        Gate *except = nullptr);
  Gate *find_and_lits (vector<int> &rhs, Gate *except = nullptr);

  Gate *find_and_lits (literal_iterator begin, literal_iterator end,
                       Gate *except = nullptr);

  Gate *find_xor_lits (const vector<int> &rhs);
  Gate *find_xor_gate (const Gate *const);

  // not const to normalize negations, also fixes the order of the LRAT
  // chain
  Gate *find_ite_gate (Gate *, bool &);

  Gate *new_ite_gate (int lhs, int cond, int then_lit, int else_lit,
                      std::vector<LitClausePair> &&clauses);
  Gate *new_and_gate (Clause *, int);
  Gate *new_xor_gate (const vector<LitClausePair> &, int);

  /*------------------------------------------------------------------------*/
  // Gate Extraction out of the clauses

  // Extraction of AND gates
  void extract_and_gates ();
  void init_and_gate_extraction ();
  void extract_and_gates_with_base_clause (Clause *c);
  Gate *find_first_and_gate (Clause *base_clause, int lhs);
  Gate *find_remaining_and_gate (Clause *base_clause, int lhs);

  // XOR gate extraction
  void init_xor_gate_extraction (std::vector<Clause *> &candidates);
  void extract_xor_gates ();
  void extract_xor_gates_with_base_clause (Clause *c);
  Clause *find_large_xor_side_clause (std::vector<int> &lits);
  void reset_xor_gate_extraction ();

  // ITE extraction. This is the most complicated code because we need to go
  // over all ternary gates.
  void extract_ite_gates ();
  void merge_condeq (int cond, lit_equivalences &condeq,
                     lit_equivalences &not_condeq);
  void find_conditional_equivalences (int lit, lit_implications &condbin,
                                      lit_equivalences &condeq);
  void copy_conditional_equivalences (int lit, lit_implications &condbin);
  void extract_ite_gates_of_literal (int);
  void extract_ite_gates_of_variable (int idx);
  void extract_condeq_pairs (int lit, lit_implications &condbin,
                             lit_equivalences &condeq);
  void init_ite_gate_extraction (std::vector<ClauseSize> &candidates);
  lit_implications::const_iterator find_lit_implication_second_literal (
      int lit, lit_implications::const_iterator begin,
      lit_implications::const_iterator end);
  void search_condeq (int lit, int pos_lit,
                      lit_implications::const_iterator pos_begin,
                      lit_implications::const_iterator pos_end, int neg_lit,
                      lit_implications::const_iterator neg_begin,
                      lit_implications::const_iterator neg_end,
                      lit_equivalences &condeq);
  void reset_ite_gate_extraction ();

  /*------------------------------------------------------------------------*/
  // Proof production specific functions

  // DRAT proofs function. For DRAT proof we sometimes have to learn extra
  // clauses that do not live very long. Those intermediate clauses are
  // stored and very soon removed. We usually do not need those extra
  // clauses in LRAT as we can produce the resolution chain directly, but
  // the resulting clause often needs probing on one decision to find the
  // conflict.
  LRAT_ID check_and_add_to_proof_chain (vector<int> &clause);
  void delete_proof_chain ();
  void add_ite_turned_and_binary_clauses (Gate *g);
  // proof. If delete_id is non-zero, then delete the clause instead of
  // learning it
  LRAT_ID simplify_and_add_to_proof_chain (vector<int> &unsimplified,
                                           LRAT_ID delete_id = 0);

  // LRAT production for merging LRAT gates
  void produce_lrat_chain_for_xor_merge (Gate *g, int lhs1,
                                         const vector<LitClausePair> &,
                                         int lhs2, vector<LRAT_ID> &,
                                         vector<LRAT_ID> &);
  void add_xor_shrinking_proof_chain (Gate *g, int src);
  void add_ite_matching_proof_chain (Gate *g, Gate *h, int lhs1, int lhs2,
                                     std::vector<LRAT_ID> &reasons1,
                                     std::vector<LRAT_ID> &reasons2);

  // and gates
  void learn_congruence_unit_falsifies_lrat_chain (Gate *g, int src,
                                                   int dst, int clashing,
                                                   int falsified, int unit);
  // when the AND gate is reduced to arity one and the LHS is already set,
  // then we produce the reason for the units.
  void learn_congruence_unit_when_lhs_set (Gate *g, int src, LRAT_ID id1,
                                           LRAT_ID id2, int dst);

  /*------------------------------------------------------------------------*/
  // TODO checking that implies
  void check_ite_implied (int lhs, int cond, int then_lit, int else_lit);
  void check_ite_gate_implied (Gate *g);
  void check_and_gate_implied (Gate *g);
  void check_ite_lrat_reasons (Gate *g);
  void check_xor_gate_implied (Gate const *const);
  void check_ternary (int a, int b, int c);
  void check_binary_implied (int a, int b);
  void check_implied ();

  /*------------------------------------------------------------------------*/
  // forward subsumption
  void forward_subsume_matching_clauses ();
  void subsume_clause (Clause *subsuming, Clause *subsumed);
  bool find_subsuming_clause (Clause *c);

  /*------------------------------------------------------------------------*/
  // learn units. You can delay units if you want to learn several at once
  // before propagation. Otherwise, propagate!
  //
  // The function can also learn the empty clause if the unit is already
  // set. Do not add the unit in the chain!
  bool learn_congruence_unit (int unit);
  bool fully_propagate ();

  /*------------------------------------------------------------------------*/
  // binary extraction and ternary strengthening
  void extract_binaries ();
  bool find_binary (int, int) const;

  /*------------------------------------------------------------------------*/
  // rewrite the clause using eager rewriting and rew1 and rew2, except for
  // 2 literals Usage:
  //   - the except are used to ignore LHS of gates that have not and should
  //   not be rewritten.
  Clause *rewrite_clause (Clause *c, int execept_lhs = 0,
                          bool remove_units = true, bool = false);
  // Rewrites the clauses in a vector of LitClausePair without removing
  // tautologies from the clause.
  void rewrite_clauses (vector<LitClausePair> &, int execept_lhs = 0,
                        bool = true);
  // Produce the rewritten clause into clause without creating a new clause
  void rewrite_clause_to_clause_vector (Clause *c, int except);

  // rewrite clauses and removes tautology
  void rewrite_clauses_and_clean (vector<LitClausePair> &,
                                  int execept_lhs = 0, bool = true,
                                  bool = false);
  // rewrite clauses in an optional clause, cleaning up if the result is a
  // tautology.
  void rewrite_clauses_and_clean (my_dummy_optional &, int execept_lhs = 0,
                                  bool = true);
  // rewrites clauses and updates the indices after removing the tautologies
  // and remove the tautological clauses
  void rewrite_clauses_and_clean (std::vector<LitClausePair> &litIds,
                                  int except_lhs, size_t &old_position1,
                                  size_t &old_position2,
                                  bool remove_units = true);

  /*------------------------------------------------------------------------*/
  // Clause handling for LRAT: we produce extra clauses that are only local
  // to the algorithm, unless we promote them to real clauses.
  Clause *new_tmp_clause (std::vector<int> &clause);
  Clause *maybe_promote_tmp_binary_clause (Clause *);
  void check_not_tmp_binary_clause (Clause *c);
  Clause *new_clause ();

  // learns a binary clause if we are not in the case that a literal is
  // unit.
  Clause *maybe_add_binary_clause (int a, int b);
  // add binary clause unconditionnaly.
  Clause *add_binary_clause (int a, int b);
  // add tmp clause
  Clause *add_tmp_binary_clause (int a, int b);

  /*------------------------------------------------------------------------*/
  // Various sorting functions to sort literals in the proper order
  //
  // sort a vector of literals
  void sort_literals_by_var (vector<int> &rhs);
  // sort the rhs of a gate
  void sort_literals_by_var (Gate *rhs);
  // sort the literals in a gate except for two literals that should be put
  // first
  void sort_literals_by_var_except (vector<int> &rhs, int, int except2 = 0);

  // XOR handling
  uint32_t number_from_xor_reason_reversed (const std::vector<int> &rhs);
  uint32_t number_from_xor_reason (const std::vector<int> &rhs, int,
                                   int except2 = 0, bool flip = 0);
  // Sort the literals within the reasons of an XOR gate.
  void gate_sort_lrat_reasons (std::vector<LitClausePair> &, int,
                               int except2 = 0, bool flip = 0);
  // Sort the literals within the reasons of an XOR gate.
  void gate_sort_lrat_reasons (LitClausePair &, int, int except2 = 0,
                               bool flip = 0);

  void schedule_literal (int lit);
  void add_clause_to_chain (std::vector<int>, LRAT_ID);

  /*------------------------------------------------------------------------*/
  // we define our own wrapper as cadical has otherwise a non-compatible
  // marking system
  signed char &marked (int lit);
  void set_mu1_reason (int lit, Clause *c);
  void set_mu2_reason (int lit, Clause *c);
  void set_mu4_reason (int lit, Clause *c);
  LitClausePair marked_mu1 (int lit);
  LitClausePair marked_mu2 (int lit);
  LitClausePair marked_mu4 (int lit);

  /*------------------------------------------------------------------------*/
  // Transform and normalize and convert ITEs to other gates. We have a huge
  // number of functions to handle various aspects of it. Most of it is
  // inlined in Kissat, but with LRAT it became just too long and too
  // complicated to even be able to read the rewrite function.

  // rewrite ITE gate g, g->lhs = cond ? then_lit : else_lit to the new type
  // tag, which is either an XOR gate or an AND gate. Then checks if the
  // gate already exists and merges them.
  //
  // The update to an XOR gate is done here, as it is rather regular, but
  // nor for AND gates.
  bool rewrite_ite_gate_to_xor_or_and (Gate *g, Gate_Type tag, int src,
                                       int dst, GatesTable::iterator git,
                                       int cond, int then_lit,
                                       int else_lit);

  // When we get a gate of the forem cond ? then_lit : !then_lit, we can
  // convert it to the xor gate !(cond ^then_lit). However, there are
  // special cases when lhs==cond, -lhs==cond, -lhs==then_lit, making it
  // possible to assigns one unit (the lhs to true or false) or prove
  // unsatisifiability if the literal is already assigned.
  //
  // We initially expected that propagations would take care of assigning
  // those new units, but this is only the case after rewriting the clauses.
  // Therefore we actually assign it here instead of waiting to make the
  // clausal congruence stronger.
  //
  // We need extra clauses for DRAT, similar to those that are produced by
  // rewriting the clauses for LRAT.
  //
  // Returns whethe the clause is garbage or not.
  bool rewrite_ite_gate_else_to_not_then (Gate *g, int, int, int);

  // Transforms an ITE gate to an AND gate, taking care of the special cases
  // where some values are already set.
  bool rewrite_ite_gate_to_and (Gate *g, int dst, int src, size_t c,
                                size_t d,
                                int cond_lit_to_learn_if_degenerated);
  // Transforms the former ITE gate to an XOR, taking care of the special
  // case with the LHS already in the RHS and updating the clauses in the
  // gate.
  bool rewrite_ite_gate_to_xor (Gate *g);

  // Simplifies the ITE gate lhs := cond ? then_lit : then_lit to "lhs =
  // then_lit", producing the lrat reasons for the merge. The function also
  // takes care of the case lhs == cond or lhs == -cond where several gate
  // clauses are missing.
  void produce_ite_merge_then_else_reasons (
      Gate *g, int dst, int src, std::vector<LRAT_ID> &reasons_implication,
      std::vector<LRAT_ID> &reasons_back);

  // Special case of ITE gate -dst := cond ? dst : else, leading do the unit
  // -cond and the merge -dst == else. For degenerated cases, we failed to
  // produce the lrat reason for the merge and first derive the unit.
  bool produce_ite_merge_lhs_then_else_reasons (Gate *g, bool, int);

  // Produce unit c out of ITE gate c := c ? !e : e.
  void produce_ite_merge_rhs_cond (Gate *g, int, int);
  // Updates the reason clauses after rewriting in an ITE gate, assuming
  // that it is not a special case and remains an ITE gate.
  void rewrite_ite_gate_update_lrat_reasons (Gate *g, int src, int dst);
  // Generates the LRAT proof for deriving a unit clause when an ITE's
  // `then` and `else` branches are both true (simplifying `lhs = (cond ?
  // true : true)` to `lhs`) or both false (simplifying `lhs = (cond ? false
  // : false)` to
  // `~lhs`).
  void simplify_ite_gate_produce_unit_lrat (Gate *g, int lit, size_t idx1,
                                            size_t idx2);

  // Transforms an ITE (If-Then-Else) gate into an AND gate when unit
  // propagation assigns values to the condition or then/else branches if
  // possible. Returns `true` if the gate degenerates to a learned unit
  // clause, `false` for successful AND gate transformation.
  //
  // The first index is a binary clause after unit propagation and the
  // second has length 3
  bool simplify_ite_gate_to_and (Gate *g, size_t idx1, size_t idx2,
                                 int removed);
  // Generates the LRAT proof chain for merging ITE gates where the `then`
  // and `else` branches are identical (i.e., trivial case `lhs = (cond ? x
  // : x)` simplifying to `lhs = x`). This function assumes that no
  // rewriting is possible!
  void produce_lrat_for_ite_merge_same_then_else_lrat (
      std::vector<LitClausePair> &clauses,
      std::vector<LRAT_ID> &reasons_implication,
      std::vector<LRAT_ID> &reasons_back);
  // Produces the LRAT proof for simplifying ITE gates when both `then` and
  // `else` branches have assigned values (one true, one false), reducing
  // the ITE to a direct equivalence `lhs = cond` or `lhs = ~cond`. It
  // generates proof chains for the two relevant clauses indexed by idx1 and
  // idx2 in the clauses.
  void simplify_ite_gate_then_else_set (
      Gate *g, std::vector<LRAT_ID> &reasons_implication,
      std::vector<LRAT_ID> &reasons_back, size_t idx1, size_t idx2);

  // produces the lrat proof chain for an ITE when the cond is set to
  // true or false.
  void simplify_ite_gate_condition_set (
      Gate *g, std::vector<LRAT_ID> &reasons_lrat,
      std::vector<LRAT_ID> &reasons_back_lrat, size_t idx1, size_t idx2);
  // normalize the sign and order of the literals in ITE gates
  bool normalize_ite_lits_gate (Gate *rhs);
};

} // namespace CaDiCaL

#endif
