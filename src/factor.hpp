#ifndef _factor_hpp_INCLUDED
#define _factor_hpp_INCLUDED

#include "clause.hpp"
#include "heap.hpp"

namespace CaDiCaL {

struct Internal;

struct factored_ite_gate {
  int definition;
  int condition;
  int true_branch;
  int false_branch;
  factored_ite_gate (int d, int c, int t, int f)
      : definition (d), condition (c), true_branch (t), false_branch (f) {}
};

struct factor_occs_size {
  Internal *internal;
  factor_occs_size (Internal *i) : internal (i) {}
  bool operator() (unsigned a, unsigned b);
};

struct Quotient {
  Quotient (int f) : factor (f), second (0), third (0) {}
  ~Quotient () {}
  int factor;
  int second; // xor
  int third;  // ite
  size_t id;
  int64_t bid; // for LRAT
  Quotient *prev, *next;
  vector<Clause *> qlauses;
  vector<size_t> matches;
  size_t matched;
};

typedef heap<factor_occs_size> FactorSchedule;

struct Factoring {
  Factoring (Internal *, int64_t);
  ~Factoring ();

  // These are initialized by the constructor
  Internal *internal;
  int64_t limit;
  FactorSchedule schedule;

  int initial;
  int bound;
  bool redundant;
  vector<unsigned> count;
  vector<vector<int>> fresh;
  vector<int> counted;
  vector<int> nounted;
  vector<Clause *> flauses;
  struct {
    Quotient *first, *last;
    Quotient *xorites;
  } quotients;
};

} // namespace CaDiCaL

#endif
