#ifndef _observer_hpp_INCLUDED
#define _observer_hpp_INCLUDED

namespace CaDiCaL {

// Proof observer class used to act on added, derived or deleted clauses.

class Observer {

public:

  Observer () { }
  virtual ~Observer () { }

  // An online proof 'Checker' needs to know original clauses too while a
  // proof 'Tracer' will not implement this function.
  //
  virtual void add_original_clause (const vector<int> &) { }

  // Notify the observer that a new clause has been derived.
  //
  virtual void add_derived_clause (const vector<int> &) { }

  // Notify the observer that a clause is not used anymore.
  //
  virtual void delete_clause (const vector<int> &) { }

  virtual void flush () { }
};

}

#endif
