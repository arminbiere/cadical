#ifndef _vivify_hpp_INCLUDED
#define _vivify_hpp_INCLUDED

namespace CaDiCaL {

struct Clause;

struct Vivifier {
  vector<Clause *> schedule, stack;
  vector<int> sorted;
  bool redundant_mode;
  std::vector<std::tuple<int, Clause *, bool>> lrat_stack;
  Vivifier (bool mode) : redundant_mode (mode) {}

  void erase () {
    erase_vector (schedule);
    erase_vector (sorted);
    erase_vector (stack);
  }
};

} // namespace CaDiCaL

#endif
