#ifndef _external_hpp_INCLUDED
#define _external_hpp_INCLUDED

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

using namespace std;

/*------------------------------------------------------------------------*/

// The CaDiCaL code is split into three layers:
//
//   Solver:       facade object providing the actual API of the solver
//   External:     communication layer between 'Solver' and 'Internal'
//   Internal:     the actual solver code
//
// Note, that 'Solver' is defined in 'cadical.hpp' and 'solver.cpp', while
// 'External' and 'Internal' in '{external,internal}.{hpp,cpp}'.
//
// Also note, that 'App' accesses (and any user of the library should
// access) the library only through the 'Solver' API.  For the library
// internal 'Parser' code we make an exception and allow access to both
// 'External' and 'Internal'.  The former to enforce the same external to
// internal mapping of variables and the latter for profiling and messages.
//
// The 'External' class provided here stores the information needed to map
// external variable indices to internal variables (actually literals).
// This is helpful for shrinking the working size of the internal solver
// after many variables become inactive.  It will also help to provide
// support for extended resolution in the future, since it allows to
// introduce only internally visible variables (even though we do not know
// how to support generating incremental proofs in this situation yet).
//
// External literals are usually called 'elit' and internal 'ilit'.

/*------------------------------------------------------------------------*/

struct Clause;
struct Internal;

struct External {

  /*----------------------------------------------------------------------*/

  typedef signed char signed_char;

  /*----------------------------------------------------------------------*/

  Internal * internal;    // The actual internal solver.
  int max_var;            // External maximum variable index.
  size_t vsize;
  vector<bool> vals;      // Current external (extended) assignment.
  vector<int> e2i;        // External 'idx' to internal 'lit' [1,max_var].

  vector<int> assumptions;      // External assumptions.

  /*----------------------------------------------------------------------*/

  // These two just factor out common sanity (assertion) checking code.

  inline int vidx (int elit) const {
    assert (elit);
    assert (elit != INT_MIN);
    int res = abs (elit);
    assert (res <= max_var);
    return res;
  }

  inline int vlit (int elit) const {
    assert (elit);
    assert (elit != INT_MIN);
    assert (abs (elit) <= max_var);
    return elit;
  }

  /*----------------------------------------------------------------------*/

  // The extension stack for reconstructing complete satisfying assignments
  // (models) of the original external formula is kept in this external
  // solver object. It keeps track of blocked clauses and clauses containing
  // eliminated variable.  These irredundant clauses are stored in terms of
  // external literals on the 'extension' stack after mapping the
  // internal literals given as arguments with 'externalize'.

  bool extended;          // Have been extended.
  vector<int> extension;  // Extension stack for reconstructing solutions.

  // The following five functions push individual literals or clauses on the
  // extension stack.  They all take internal literals as argument, and map
  // them back to external literals first, before pushing them on the stack.

  void push_zero_on_extension_stack ();

  // Our general version of extension stacks always pushes a set of witness
  // literals (for variable elimination the literal of the eliminated
  // literal and for blocked clauses the blocking literal) followed by all
  // the clause literals starting with and separated by zero.
  //
  void push_clause_literal_on_extension_stack (int ilit);
  void push_witness_literal_on_extension_stack (int ilit);

  void push_clause_on_extension_stack (Clause *, int witness);
  void push_binary_clause_on_extension_stack (int witness, int other);

  // The main 'extend' function which extends an internal assignment to an
  // external assignment using the extension stack (and sets 'extended').
  //
  void extend ();

  /*----------------------------------------------------------------------*/

  // Marking external literals.

  unsigned elit2ulit (int elit) const {
    assert (elit);
    assert (elit != INT_MIN);
    const int idx = abs (elit) - 1;
    assert (idx <= max_var);
    return 2u*idx + (elit < 0);
  }

  bool marked (const vector<bool> & map, int elit) const {
    const unsigned ulit = elit2ulit (elit);
    return ulit < map.size () ? map[ulit] : false;
  }

  void mark (vector<bool> & map, int elit) {
    const unsigned ulit = elit2ulit (elit);
    while (ulit >= map.size ()) map.push_back (false);
    map[ulit] = true;
  }

  void unmark (vector<bool> & map, int elit) {
    const unsigned ulit = elit2ulit (elit);
    if (ulit < map.size ()) map[ulit] = false;
  }

  vector<bool> witness;
  vector<bool> tainted;

  /*----------------------------------------------------------------------*/

  void push_external_clause_and_witness_on_extension_stack (
    const vector<int> & clause, const vector<int> & witness);

  // Restore a clause, which was pushed on the extension stack.
  //
  void restore_clause (
    const vector<int>::const_iterator & begin,
    const vector<int>::const_iterator & end);

  void restore_clauses ();

  /*----------------------------------------------------------------------*/

  // Explicitly freeze and melt literals (instead of just freezing
  // internally and implicitly assumed literals).  Passes on freezing and
  // melting to the internal solver, which has separate frozen counters.

  vector<unsigned> frozentab;

  void freeze (int elit);
  void melt (int elit);

  bool frozen (int elit) {
    assert (elit);
    assert (elit != INT_MIN);
    int eidx = abs (elit);
    if (eidx > max_var) return false;
    if (eidx >= (int) frozentab.size ()) return false;
    return frozentab[eidx] > 0;
  }

  // Used if 'checkfrozen' is set to make sure that only literals are added
  // which were never completely molten before.  These molten literals are
  // marked at the beginning of the 'solve' call.  Note that variables
  // larger than 'max_var' are not molten and can be used in the future.
  //
  vector<bool> moltentab;

  /*----------------------------------------------------------------------*/

  External (Internal *);
  ~External ();

  void enlarge (int new_max_var);       // Enlarge allocated 'vsize'.
  void init (int new_max_var);          // Initialize up-to 'new_max_var'.

  int internalize (int);        // Translate external to internal literal.

  /*----------------------------------------------------------------------*/

  // According to the CaDiCaL API contract (as well as IPASIR) we have to
  // forget about the previous assumptions after a 'solve' call.  This
  // should however be delayed until we transition out of an 'UNSATISFIED'
  // state, i.e., after no more 'failed' calls are expected.  Note that
  // 'failed' requires to know the failing assumptions, and the 'failed'
  // status of those should cleared before at start of the next 'solve'.
  // As a consequence 'reset_assumptions' is only called from
  // 'transition_to_unknown_state' in API calls in 'solver.cpp'.

  void reset_assumptions ();

  // Similarly a valid external assignment obtained through 'extend' has to
  // be reset at each point it risks to become invalid.  This is done
  // in the external layer in 'external.cpp' functions..

  void reset_extended ();

  // Finally, the semantics of incremental solving also require that limits
  // are only valid for the next 'solve' call.  Since the limits can not
  // really be queried, handling them is less complex and they are just
  // reset immediately at the end of 'External::solve'.

  void reset_limits ();

  /*----------------------------------------------------------------------*/

  // Proxies to IPASIR functions.

  void add (int elit);
  void assume (int elit);
  int solve ();
  void terminate ();

  inline int val (int elit) const {
    assert (elit != INT_MIN);
    int eidx = abs (elit), res;
    if (eidx > max_var) res = -1;
    else if ((size_t) eidx >= vals.size ()) res = -1;
    else res = vals[eidx] ? eidx : -eidx;
    if (elit < 0) res = -res;
    return res;
  }

  int fixed (int elit) const;   // Implemented in 'internal.hpp'.

  bool failed (int elit);

  /*----------------------------------------------------------------------*/

  // Regularly checked terminator if non-zero.  The terminator is set from
  // 'Solver::set (Terminator *)' and checked by 'Internal::terminating ()'.

  Terminator * terminator;

  /*----------------------------------------------------------------------*/

  signed char * solution; // For checking & debugging [1,max_var]
  vector<int> original;   // Saved original formula for checking.

  // For debugging and testing only.  See 'solution.hpp' for more details.
  //
  inline int sol (int elit) const {
    assert (solution);
    assert (elit != INT_MIN);
    int eidx = abs (elit);
    if (eidx > max_var) return 0;
    int res = solution[eidx];
    if (elit < 0) res = -res;
    return res;
  }

  /*----------------------------------------------------------------------*/

  void check_assumptions_satisfied ();
  void check_assumptions_failing ();

  void check_solution_on_learned_clause ();
  void check_solution_on_shrunken_clause (Clause *);
  void check_solution_on_learned_unit_clause (int unit);
  void check_no_solution_after_learning_empty_clause ();

  void check_learned_empty_clause () {
    if (solution) check_no_solution_after_learning_empty_clause ();
  }

  void check_learned_unit_clause (int unit) {
    if (solution) check_solution_on_learned_unit_clause (unit);
  }

  void check_learned_clause () {
    if (solution) check_solution_on_learned_clause ();
  }

  void check_shrunken_clause (Clause * c) {
    if (solution) check_solution_on_shrunken_clause (c);
  }

  void check_assignment (int (External::*assignment) (int) const);

  void check_satisfiable ();
  void check_unsatisfiable ();

  void check_solve_result (int res);

  void update_molten_literals ();

  /*----------------------------------------------------------------------*/

  // Traversal functions.

  bool traverse_all_frozen_units_as_clauses (ClauseIterator &);
  bool traverse_all_non_frozen_units_as_witnesses (WitnessIterator &);
  bool traverse_witnesses_backward (WitnessIterator &);
  bool traverse_witnesses_forward (WitnessIterator &);
};

}

#endif
