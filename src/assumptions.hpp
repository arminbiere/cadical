#include "inttypes.hpp"

// Common 'C++' headers.

#include <algorithm>
#include <queue>
#include <string>
#include <unordered_set>
#include <vector>

namespace CaDiCaL {

class Assumptions {
public:
  
  bool satisfied (); // check if all literals have been consumed
  size_t level (); // number of levels
  int next ();     // return next not yet assigned assumption
  void backtrack (unsigned level); // goes back to the level
  void add (int assumption); // add a literal to the assumption
  void clear (); // reset the assumptions
  void reset_ilb (unsigned level); // backtrack in the case of ILB to reset invariants
  void decide (); // set the last next () to be set
  size_t size (); // size of the assumptions
  auto begin () {return std::begin (assumptions);};
  auto end () {return std::end (assumptions);};
  bool empty () {return assumptions.empty ();};
  int & operator[] (int i) {return assumptions [i];};
  void pop (); // pop the last literal back to the stream
  
  std::vector<int> assumptions;
  std::vector<int> control = {0};
  size_t assumed = 0;
};

}