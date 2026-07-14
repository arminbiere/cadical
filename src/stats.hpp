#ifndef _stats_hpp_INCLUDED
#define _stats_hpp_INCLUDED

#include "statistics.hpp"
#include <cstdint>
#include <cstdlib>
#include <vector>

namespace CaDiCaL {

struct Internal;

#ifndef NMETRICS
struct Metric {
  int64_t val;
  Metric (int64_t x) : val (x) {}
  Metric operator+= (int64_t x) {
    val += x;
    return *this;
  }
  Metric operator+= (Metric x) {
    val += x.val;
    return *this;
  }
  Metric &operator++ (int) {
    val++;
    return *this;
  }
  Metric &operator++ () {
    ++val;
    return *this;
  }
  int64_t operator- (int64_t t) { return val - t; }
  Metric &operator= (int64_t x) {
    val = x;
    return *this;
  }
  int64_t operator+ (int64_t t) { return t + val; }
  operator double () const { return (double) val; }
  explicit operator int64_t () const { return val; }
  explicit operator bool () const { return val; }
};
#else
struct Metric {
  Metric (int64_t) {}
  Metric operator+= (int64_t) { return *this; }
  Metric operator+= (Metric) { return *this; }
  Metric &operator++ (int) { return *this; }
  Metric &operator++ () { return *this; }
  Metric &operator= (int64_t) { return *this; }
  int64_t operator- (int64_t) { return 0; }
  int64_t operator+ (int64_t) { return 0; }
  explicit operator int64_t () const { return 0; }
  explicit operator bool () const {
    assert (false);
    return 0;
  }
};
#endif

struct Stats {

  Internal *internal;

#define STATISTIC(NAME, VERBOSE, COMMAND, SYMBOL, OTHER) int64_t NAME = 0;
#define METRIC(NAME, VERBOSE, COMMAND, SYMBOL, OTHER) Metric NAME = 0;

  CADICAL_STATISTICS

#undef STATISTIC
#undef METRIC

  struct {
    double real = 0;
    double process = 0;
  } time;

  uint64_t bump_used[2] = {0, 0};
  std::vector<uint64_t> used[2] = {{}, {}}; // used clauses in focused mode
  int64_t walk_minimum;

  Stats ();
  ~Stats () = default;

  void print (Internal *);
#ifndef QUIET
  void print_internal_stats (Internal *);
#endif
};

/*------------------------------------------------------------------------*/

} // namespace CaDiCaL

#endif
