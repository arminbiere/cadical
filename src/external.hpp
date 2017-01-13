#ifndef _external_hpp_INCLUDED
#define _external_hpp_INCLUDED

#include <vector>
#include <climits>
#include <cstdlib>
#include <cassert>

namespace CaDiCaL {

using namespace std;

class Clause;
class Internal;

class External {

  friend class Internal;
  friend class Parser;
  friend class Solver;

  /*----------------------------------------------------------------------*/

  size_t vsize;           // actually allocated variable data size
  int max_var;            // (exernal) maximum variable index
  signed char * vals;	  // external assignment [1,max_var]
  signed char * solution; // for debugging       [-max_var,max_var]
  int * map;		  // external idx to internal lit [1,max_var]

  vector<int> extension;
  vector<int> original;

  Internal * internal;

  /*----------------------------------------------------------------------*/

  void push_on_extension_stack (Clause *, int pivot);
  void extend ();

  External (Internal *);
  ~External ();

  void enlarge (int new_max_var);
  void resize (int new_max_var);

  int vidx (int lit) const {
    assert (lit != INT_MIN);
    const int res = abs (lit);
    assert (res), assert (res <= max_var);
    return res;
  }

  int internalize (int lit) const {
    int res = map[vidx (lit)];
    if (lit < 0) res = -res;
    return res;;
  }

  void add (int lit);

  int solve ();

  int val (int lit) const {
    assert (lit != INT_MIN);
    int idx = abs (lit);
    if (idx > max_var) return 0;
    int res = vals[idx];
    if (lit < 0) res = -res;
    return res;
  }

  int sol (int lit) const {
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
