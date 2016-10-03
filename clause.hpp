#ifndef _clause_hpp_INCLUDED
#define _clause_hpp_INCLUDED

#include <cstdlib>

struct Clause {

  long resolved;     // time stamp when resolved last time
                    
  bool redundant;    // aka 'learned' so not 'irredundant' (original)
  bool garbage;      // can be garbage collected unless it is a 'reason'
  bool reason;       // reason / antecedent clause can not be collected

  int glue;          // glue = glucose level = LBD
  int size;          // actual size of 'literals' (at least 2)

  int literals[2];   // actually of variadic 'size' in general

  static size_t bytes (int size) {
    return sizeof (Clause) + (size -2 ) * sizeof (int);
  }

  size_t bytes () const { return bytes (size); }
};

#endif
