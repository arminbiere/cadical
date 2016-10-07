#ifndef _stats_hpp_INCLUDED
#define _stats_hpp_INCLUDED

#include <cstdlib>

namespace CaDiCaL {

class Solver;

struct Stats {

  Solver * solver;

  long conflicts;
  long decisions;
  long propagations;            // propagated literals in 'propagate'

  struct {
    long count;                 // actual number of happened restarts
    long tried;                 // number of tried restarts
    long reused;                // number of reused trails
  } restart;

  long reports;                 // 'report' counter
  long sections;                // 'section' counter

  long bumped;                  // seen and bumped variables in 'analyze'
  long resolved;                // resolved redundant clauses in 'analyze'
  long searched;                // searched decisions in 'decide'

  struct { long count, clauses, bytes; } reduce; // in 'reduce'
  struct { long learned, minimized; } literals;  // in 'minimize_clause'

  struct { long redundant, irredundant, current, max; } clauses;
  struct { struct { size_t current, max; } total, watcher; } bytes;

  struct { long unit, binary; } learned;

  int fixed;                    // top level assigned variables

  Stats (Solver *);
  void print ();
};

};

#endif
