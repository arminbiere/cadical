#ifndef _lratbuilder_hpp_INCLUDED
#define _lratbuilder_hpp_INCLUDED

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// This constructs lrat-style proof chains. Enabled by 'opts.externallrat'
// in essence this implements the same propagation routine as the DRUP
// checker but also stores the reason for each assignment. The proof chain
// is then recreated from that.

/*------------------------------------------------------------------------*/

struct LratBuilderClause {
  LratBuilderClause *next; // collision chain link for hash table
  uint64_t hash;           // previously computed full 64-bit hash
  uint64_t id;             // id of clause
  bool garbage;            // for garbage clauses
  unsigned size;
  int literals[1]; // 'literals' of length 'size'
};

struct LratBuilderWatch {
  int blit;
  unsigned size;
  LratBuilderClause *clause;
  LratBuilderWatch () {}
  LratBuilderWatch (int b, LratBuilderClause *c)
      : blit (b), size (c->size), clause (c) {}
};

typedef vector<LratBuilderWatch> LratBuilderWatcher;

/*------------------------------------------------------------------------*/

class LratBuilder {

  Internal *internal;

  // Capacity of variable values.
  //
  int64_t size_vars;

  // For the assignment we want to have an as fast access as possible and
  // thus we use an array which can also be indexed by negative literals and
  // is actually valid in the range [-size_vars+1, ..., size_vars-1].
  //
  signed char *vals;

  // The 'watchers' and 'marks' data structures are not that time critical
  // and thus we access them by first mapping a literal to 'unsigned'.
  //
  static unsigned l2u (int lit);
  vector<LratBuilderWatcher> watchers; // watchers of literals
  vector<signed char> marks;           // mark bits of literals

  signed char &mark (int lit);
  signed char &checked_lit (int lit);
  LratBuilderWatcher &watcher (int lit);

  // access by abs(lit)
  static unsigned l2a (int lit);
  vector<LratBuilderClause *> reasons;      // reason for each assignment
  vector<LratBuilderClause *> unit_reasons; // units get preferred
  vector<bool> justified;
  vector<bool> todo_justify;
  vector<signed char> checked_lits; // this is implemented same as marks
  LratBuilderClause *conflict;

  vector<uint64_t> chain; // LRAT style proof chain
  vector<uint64_t> reverse_chain;
  vector<uint64_t> inconsistent_chain; // store proof to reuse
  unsigned unjustified;                // number of lits to justify

  bool new_clause_taut;
  bool inconsistent; // found or added empty clause

  uint64_t num_clauses;        // number of clauses in hash table
  uint64_t num_garbage;        // number of garbage clauses
  uint64_t size_clauses;       // size of clause hash table
  LratBuilderClause **clauses; // hash table of clauses
  LratBuilderClause *garbage;  // linked list of garbage clauses

  vector<int> unsimplified; // original clause for reporting
  vector<int> simplified;   // clause for sorting

  vector<int> trail; // for propagation

  unsigned next_to_propagate; // next to propagate on trail

  void enlarge_vars (int64_t idx);
  void import_literal (int lit);
  void import_clause (const vector<int> &);
  void tautological ();
  LratBuilderClause *assumption;
  LratBuilderClause *inconsistent_clause;
  vector<LratBuilderClause *>
      unit_clauses; // we need this because propagate
                    // cannot propagate unit clauses
  static const unsigned num_nonces = 4;

  uint64_t nonces[num_nonces];      // random numbers for hashing
  uint64_t last_hash;               // last computed hash value of clause
  uint64_t last_id;                 // id of the last added clause
  uint64_t compute_hash (uint64_t); // compute and save hash value of clause

  // Reduce hash value to the actual size.
  //
  static uint64_t reduce_hash (uint64_t hash, uint64_t size);

  void enlarge_clauses ();      // enlarge hash table for clauses
  LratBuilderClause *insert (); // insert clause in hash table
  LratBuilderClause **
  find (const uint64_t); // find clause position in hash table

  void add_clause (const char *type);
  void clean (); // cleans up after adding/deleting clauses

  void collect_garbage_clauses ();

  LratBuilderClause *new_clause ();
  void delete_clause (LratBuilderClause *);

  signed char val (int lit); // returns '-1', '0' or '1'

  bool clause_satisfied (LratBuilderClause *);
  bool clause_falsified (LratBuilderClause *);

  void assign (int lit); // assign a literal to true
  void assign_reason (int lit, LratBuilderClause *reason_clause);
  void unassign_reason (int lit);
  void assume (int lit); // assume a literal

  bool unit_propagate ();
  bool propagate ();         // propagate and check for conflicts
  void backtrack (unsigned); // prepare for next clause

  // returns false if it fails to build a proof by calling one of the
  // following
  bool build_chain_if_possible ();
  // if the clause is a true tautology it needs no proof.
  void proof_tautological_clause ();
  // the following three initialize chain and justify_todo differently and
  // then call construct_chain.
  void proof_clause ();
  // for satisfied clauses we only need to prove the satisfied lit
  void proof_satisfied_literal (int lit);
  // if the state is already inconsistent we can add any clause by proving
  // the inconsistent clause
  void proof_inconsistent_clause ();
  // combining similar code from the above
  void construct_chain ();

  struct {

    int64_t added;    // number of added clauses
    int64_t original; // number of added original clauses
    int64_t derived;  // number of added derived clauses

    int64_t deleted; // number of deleted clauses

    int64_t assumptions;  // number of assumed literals
    int64_t propagations; // number of propagated literals

    int64_t insertions; // number of clauses added to hash table
    int64_t collisions; // number of hash collisions in 'find'
    int64_t searches;   // number of searched clauses in 'find'

    int64_t checks; // number of implication checks

    int64_t collections; // garbage collections
    int64_t units;

  } stats;

public:
  LratBuilder (Internal *);
  ~LratBuilder ();

  void add_original_clause (uint64_t, const vector<int> &);
  void add_derived_clause (uint64_t, const vector<int> &);
  void delete_clause (uint64_t, const vector<int> &);
  const vector<uint64_t> &add_clause_get_proof (uint64_t,
                                                const vector<int> &);

  void print_stats ();
  void dump (); // for debugging purposes only
};

} // namespace CaDiCaL

#endif
