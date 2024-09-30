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
  bool satisfied ();
  bool falsified ();
  size_t level (); // assumption level
  int failed ();   // return next failed assumption
  int next ();     // return next not yet assigned assumption
  void backtrack (unsigned level);
  void add (int assumption);
  void clear ();
  void decide (); // set the last next () to be set
  size_t size ();
  auto begin () {return std::begin (assumptions);};
  auto end () {return std::end (assumptions);};
  bool empty () {return assumptions.empty ();};
  int & operator[] (int i) {return assumptions [i];};
  
  std::vector<int> assumptions;
  std::vector<int> control = {0};
  int assumed = 0;
};

}