#ifndef _external_hpp_INCLUDED
#define _external_hpp_INCLUDED

/*------------------------------------------------------------------------*/

#include <cassert>
#include <climits>
#include <cstdlib>

/*------------------------------------------------------------------------*/

#include <vector>

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

using namespace std;

/*------------------------------------------------------------------------*/

// The CaDiCal code is split into three layers:
//
//   Solver:       facade object providing the actual API of the solver
//   External:     commmunication layer between 'Solver' and 'Internal'
//   Internal:     the actual solver code
//
// Note, that 'App' (and any user of the library should) access the library
// only through the 'Solver' API.  For the library internal 'Parser' code we
// make an exception and allow access to both 'External' and 'Internal'.
// The former to enforce the same external to internal mapping of variables
// and the latter for profiling and messages.

// The 'External' class provided here stores the information needed to map
// external variable indices to internal variables (actually literals).
// This is helpful for shrinking the working size of the internal solver if
// after many variables become inactive.  It will also help to provide
// support for extended resolution in the future, since it allows to
// introduce variables only visible internally (even though we do not know
// how to support generating incremental proofs in this situation yet).

/*------------------------------------------------------------------------*/

class Clause;
class Internal;

class External {

  friend class Internal;
  friend class Parser;
  friend class Solver;
  friend struct Stats;

  /*----------------------------------------------------------------------*/

  typedef signed char signed_char;

  /*----------------------------------------------------------------------*/

  size_t vsize;           // actually allocated variable data size
  int max_var;            // (exernal) maximum variable index
  signed char * vals;	  // external assignment [1,max_var]
  signed char * solution; // for debugging       [-max_var,max_var]
  int * e2i;		  // external idx to internal lit [1,max_var]

  vector<int> extension;
  vector<int> original;

  Internal * internal;

  /*----------------------------------------------------------------------*/

  void push_clause_on_extension_stack (Clause *, int pivot);
  void push_binary_on_extension_stack (int pivot, int other);
  void push_unit_on_extension_stack (int pivot);
  void extend ();

  External (Internal *);
  ~External ();

  void enlarge (int new_max_var);
  void init (int new_max_var);

  int vidx (int lit) const {
    assert (lit != INT_MIN);
    const int res = abs (lit);
    assert (res), assert (res <= max_var);
    return res;
  }

  int internalize (int lit) {
    int res;
    if (lit) {
      assert (lit != INT_MIN);
      const int eidx = abs (lit);
      if (eidx > max_var) init (eidx);
      res = e2i [eidx];
      if (lit < 0) res = -res;
    } else res = 0;
    return res;
  }

  void add (int lit);

  int solve ();

  inline int val (int lit) const {
    assert (lit != INT_MIN);
    int idx = abs (lit);
    if (idx > max_var) return 0;
    int res = vals[idx];
    if (lit < 0) res = -res;
    return res;
  }

  // For debugging and testing only.  See 'solution.hpp' for more details.
  //
  inline int sol (int lit) const {
    assert (solution);
    assert (lit != INT_MIN);
    int idx = abs (lit);
    if (idx > max_var) return 0;
    int res = solution[idx];
    if (lit < 0) res = -res;
    return res;
  }

  void check_solution_on_learned_clause ();
  void check_solution_on_shrunken_clause (Clause *);

  void check_learned_clause () {
    if (solution) check_solution_on_learned_clause ();
  }

  void check_shrunken_clause (Clause * c) {
    if (solution) check_solution_on_shrunken_clause (c);
  }

  void check (int (External::*assignment) (int) const);
};

};

#endif
