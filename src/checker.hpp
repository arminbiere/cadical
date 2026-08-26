#ifndef _checker_hpp_INCLUDED
#define _checker_hpp_INCLUDED

#include "tracer.hpp" // Alphabetically after 'checker'.

#include <cstdint>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// This checker implements an online forward (I)DRUP proof checker enabled
// by 'opts.checkidrup' (requires 'opts.check' also to be enabled).  This is
// useful for model basted testing (and delta-debugging), where we can not
// rely on an external proof checker such as 'drat-trim'.  We also do not
// have yet  a flow for offline incremental proof checking, while this
// checker here can also be used in an incremental setting.
//
// In essence the checker implements is a simple propagation online SAT
// solver with an additional hash table to find clauses fast for
// 'delete_clause'.  It requires its own data structure for clauses
// ('CheckerClause') and watches ('CheckerWatch').
//
// In our experiments the checker slows down overall SAT solving time by a
// factor of 3, which we contribute to its slightly less efficient
// implementation.

/*------------------------------------------------------------------------*/

struct CheckerClause {
  CheckerClause *next; // collision chain link for hash table
  uint64_t hash;       // previously computed full 64-bit hash
  int64_t id;          // id for computing hash
  bool temporary;      // constraints and assumption clauses
  bool satisfied;      // satisfied or tautological
  bool garbage;        // watched
  unsigned size;
#ifndef NFLEXIBLE
  int literals[]; // otherwise 'literals' of length 'size'
#else
  int literals[2];
#endif
};

struct CheckerWatch {
  int blit;
  unsigned size : 31;
  bool temporary : 1;
  CheckerClause *clause;
  CheckerWatch () {}
  CheckerWatch (int b, CheckerClause *c)
      : blit (b), size (c->size), temporary (c->temporary), clause (c) {}
};

typedef std::vector<CheckerWatch> CheckerWatcher;

/*------------------------------------------------------------------------*/

class Checker : public StatTracer {

  Internal *internal;
  bool check_finalize;

  // Capacity of variable values.
  //
  int64_t size_vars;

  // For the assignment we want to have an as fast access as possible and
  // thus we use an array which can also be indexed by negative literals and
  // is actually valid in the range [-size_vars+1, ..., size_vars-1].
  //
  signed char *vals;
  bool *assumed;

  // The 'watchers' and 'marks' data structures are not that time critical
  // and thus we access them by first mapping a literal to 'unsigned'.
  //
  static unsigned l2u (int lit);
  std::vector<CheckerWatcher> watchers; // watchers of literals
  std::vector<signed char> marks;       // mark bits of literals
  std::vector<int> temporary_units;

  signed char &mark (int lit);
  CheckerWatcher &watcher (int lit);

  int64_t inconsistent;     // found or added empty clause
  int64_t tmp_inconsistent; // found or added empty clause
  bool solving;

  uint64_t num_clauses;   // number of clauses in hash table
  uint64_t num_garbage;   // number of garbage clauses
  uint64_t num_finalized; // number of finalized clauses
  uint64_t num_temporary; // number of temporary clauses
  uint64_t num_permanent; // number of permanent clauses

  uint64_t size_clauses;   // size of clause hash table
  CheckerClause **clauses; // hash table of clauses
  CheckerClause *garbage;  // linked list of garbage clauses

  std::vector<int> unsimplified; // original clause for reporting
  std::vector<int> simplified;   // clause for sorting

  std::vector<int> assumptions;
  std::vector<int64_t> assumption_clauses;
  std::vector<int> trail; // for propagation

  unsigned next_to_propagate; // next to propagate on trail

  void enlarge_vars (int64_t idx);
  void import_literal (int lit);
  void import_clause (const std::vector<int> &, int64_t, bool);
  bool tautological ();

  static const unsigned num_nonces = 4;

  uint64_t nonces[num_nonces]; // random numbers for hashing
  uint64_t last_hash;          // last computed hash value of clause
  int64_t last_id;
  bool is_tmp;
  bool is_taut;
  uint64_t compute_hash (); // compute and save hash value of clause

  // Reduce hash value to the actual size.
  //
  static uint64_t reduce_hash (uint64_t hash, uint64_t size);

  void enlarge_clauses ();              // enlarge hash table
  void insert ();                       // insert into hash table
  CheckerClause **find (int64_t, bool); // find in hash table

  void add_clause (const char *type);

  void collect_garbage_clauses ();

  CheckerClause *new_clause ();
  void delete_clause (CheckerClause *);
  void move_to_garbage (CheckerClause **);

  signed char val (int lit); // returns '-1', '0' or '1'

  bool clause_satisfied (CheckerClause *);

  void assign (int lit);     // assign a literal to true
  void assume (int lit);     // assume a literal
  bool propagate (bool);     // propagate and check for conflicts
  void backtrack (unsigned); // prepare for next clause
  bool check (bool propagate_temporary =
                  false); // check simplified clause is implied
  bool check_blocked ();  // check if clause is blocked

  struct {

    int64_t added;    // number of added clauses
    int64_t original; // number of added original clauses
    int64_t derived;  // number of added derived clauses
    int64_t derived_redundant;
    int64_t derived_irredundant;
    int64_t finalized;

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
  Checker (Internal *, bool);
  virtual ~Checker ();

  void connect_internal (Internal *i) override;

  void add_original_clause (int64_t, bool, const std::vector<int> &,
                            bool = false) override;
  void add_derived_clause (int64_t, bool, int, const std::vector<int> &,
                           const std::vector<int64_t> &) override;
  void delete_clause (int64_t, bool, const std::vector<int> &) override;

  void finalize_clause (int64_t, const std::vector<int> &) override;
  void report_status (int, int64_t) override;
  void begin_proof (int64_t) override {} // skip
  void add_assumption_clause (int64_t, const std::vector<int> &,
                              const std::vector<int64_t> &) override;
  void add_constraint_clause (int64_t, const std::vector<int> &,
                              const std::vector<int64_t> &) override;

  void demote_clause (int64_t, const std::vector<int> &) override;
  void weaken_minus (int64_t, const std::vector<int> &) override;
  void strengthen (int64_t) override;
  void solve_query () override;
  void add_assumption (int) override;
  void add_constraint (int64_t, const std::vector<int> &) override;
  void reset_assumptions () override;
  void conclude_unsat (ConclusionType,
                       const std::vector<int64_t> &) override;
  void conclude_sat (const std::vector<int> &) override;
  void conclude_unknown (const std::vector<int> &) override;
  void notify_equivalence (int, int) override;

  void print_stats () override;
  void dump (); // for debugging purposes only
};

} // namespace CaDiCaL

#endif
