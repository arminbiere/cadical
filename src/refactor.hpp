#ifndef _refactor_hpp_INCLUDED
#define _refactor_hpp_INCLUDED

#include <cstdint>
#include <vector>

namespace CaDiCaL {

struct Clause;

// In the vivifier structure, we put the schedules in an array in order to
// be able to iterate over them, but we provide the reference to them to
// make sure that you do need to remember the order.
struct Refactoring {
  std::vector<std::pair<int, std::vector<Clause *>>> gate_clauses;
  std::vector<std::pair<int, Clause *>> candidates;
  int64_t ticks;
  std::vector<std::tuple<int, Clause *, bool>> lrat_stack;
};

} // namespace CaDiCaL

#endif
