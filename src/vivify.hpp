#ifndef _vivify_hpp_INCLUDED
#define _vivify_hpp_INCLUDED

#include <array>

namespace CaDiCaL {

struct Clause;

enum class Vivify_Mode { TIER1, TIER2, TIER3, IRREDUNDANT };

struct Vivifier {
  std::array<vector<Clause *>,4> schedules;
  vector<Clause *> &schedule_tier1, &schedule_tier2, &schedule_tier3, &schedule_irred;
  vector<int> sorted;
  Vivify_Mode tier;
  char tag;
  int tier1;
  int tier2;
  std::vector<std::tuple<int, Clause *, bool>> lrat_stack;
  Vivifier (Vivify_Mode mode_tier) : schedule_tier1(schedules[0]), schedule_tier2(schedules[1]),
				     schedule_tier3(schedules[2]), schedule_irred(schedules[3]),
				      tier (mode_tier) {}

  void erase () {
    erase_vector (schedule_tier1);
    erase_vector (schedule_tier2);
    erase_vector (schedule_tier3);
    erase_vector (schedule_irred);
    erase_vector (sorted);
  }

};

} // namespace CaDiCaL

#endif
