#ifndef _vivify_hpp_INCLUDED
#define _vivify_hpp_INCLUDED

namespace CaDiCaL {

struct Clause;

enum class Vivify_Mode { TIER1, TIER2, TIER3, IRREDUNDANT };

struct Vivifier {
  vector<Clause *> schedule, stack;
  vector<int> sorted;
  Vivify_Mode tier;
  char tag;
  Vivifier (Vivify_Mode mode_tier) : tier (mode_tier) {}

  void erase () {
    erase_vector (schedule);
    erase_vector (sorted);
    erase_vector (stack);
  }
};

} // namespace CaDiCaL

#endif
