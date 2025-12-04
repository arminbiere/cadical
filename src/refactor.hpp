#ifndef _refactor_hpp_INCLUDED
#define _refactor_hpp_INCLUDED

#include <cstdint>
#include <vector>

namespace CaDiCaL {

struct Clause;

struct refactor_gate {
  int definition;
  int condition;
  int true_branch;
  int false_branch;
  bool skip;
  std::vector<Clause *> clauses;
};

struct refactor_candidate {
  size_t index;
  bool negdef;
  bool negcon;
  Clause *candidate;
};
// In the vivifier structure, we put the schedules in an array in order to
// be able to iterate over them, but we provide the reference to them to
// make sure that you do need to remember the order.
struct Refactoring {
  std::vector<refactor_gate> gate_clauses;
  std::vector<refactor_candidate> candidates;
  int64_t ticks;
  std::vector<std::tuple<int, Clause *, bool>> lrat_stack;
};

} // namespace CaDiCaL

#endif
