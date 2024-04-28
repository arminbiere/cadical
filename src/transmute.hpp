#ifndef _transmute_hpp_INCLUDED
#define _transmute_hpp_INCLUDED

namespace CaDiCaL {

struct Clause;

struct Transmuter {
  vector<pair<Clause *,int>> schedule;
  vector<int> current;
  Transmuter () {}

  void erase () {
    erase_vector (schedule);
    erase_vector (current);
  }
};

} // namespace CaDiCaL

#endif
