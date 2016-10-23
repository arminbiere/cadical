#ifndef _stats_hpp_INCLUDED
#define _stats_hpp_INCLUDED

#include <cstdlib>

namespace CaDiCaL {

class Internal;

struct Stats {

  Internal * internal;

  long conflicts;    // generated conflicts in 'propagate'
  long decisions;    // number of decisions in 'decide'
  long propagations; // propagated literals in 'propagate'
  long restarts;     // actual number of happened restarts
  long reused;       // number of reused trails
  long reports;      // 'report' counter
  long sections;     // 'section' counter
  long bumped;       // seen and bumped variables in 'analyze'
  long resolved;     // resolved redundant clauses in 'analyze'
  long searched;     // searched decisions in 'decide'
  long reductions;   // 'reduce' counter
  long reduced;      // number of reduced clauses
  long collected;    // number of collected bytes
  long subsumed;     // number of subsumed clauses
  long learned;      // learned literals
  long minimized;    // minimized literals
  long redundant;    // number of current redundant clauses
  long irredundant;  // number of current irredundant clauses
  long units;        // learned unit clauses
  long binaries;     // learned binary clauses

  int fixed;         // top level assigned variables

  struct { struct { size_t current, max; } total, watcher; } bytes;

  Stats ();
  void print (Internal *);
};

};

#endif
