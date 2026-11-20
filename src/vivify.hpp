#ifndef _vivify_hpp_INCLUDED
#define _vivify_hpp_INCLUDED

#include "util.hpp"

#include <array>
#include <cstdint>
#include <vector>

namespace CaDiCaL {

struct Clause;

enum class Vivify_Mode { TIER1, TIER2, TIER3, IRREDUNDANT };

constexpr int COUNTREF_COUNTS = 2;

struct vivify_ref {
  bool vivify;
  std::size_t size;
  std::array<uint64_t, COUNTREF_COUNTS> count = {0};
  Clause *clause;
  vivify_ref () : vivify (false), size (0), clause (nullptr) {}
};

// In the vivifier structure, we put the schedules in an array in order to
// be able to iterate over them, but we provide the reference to them to
// make sure that you do need to remember the order.
struct Vivifier {
  std::vector<vivify_ref> refs_schedule;
  std::array<std::vector<Clause *>, 4> schedules;
  std::vector<int> sorted;
  Vivify_Mode tier;
  char tag = '\0';
  int tier1_limit = 0;
  int tier2_limit = 0;
  int64_t ticks = 0;
  std::vector<std::tuple<int, Clause *, bool>> lrat_stack;
  Vivifier (Vivify_Mode mode_tier) : tier (mode_tier) {}
  std::vector<Clause *> &schedule_tier1 () { return schedules[0]; }
  std::vector<Clause *> &schedule_tier2 () { return schedules[1]; }
  std::vector<Clause *> &schedule_tier3 () { return schedules[2]; }
  std::vector<Clause *> &schedule_irred () { return schedules[3]; }

  void erase () { erase_vector (sorted); }
};

} // namespace CaDiCaL

#endif
