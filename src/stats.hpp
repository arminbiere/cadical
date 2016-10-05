#ifndef _stats_hpp_INCLUDED
#define _stats_hpp_INCLUDED

namespace CaDiCaL {

class Solver;

struct Stats {
  long conflicts;
  long decisions;
  long propagations;            // propagated literals in 'propagate'

  struct {
    long count;		// actual number of happened restarts 
    long tried;		// number of tried restarts
    long unit;          // from those the number forced by low unit frequency
    long blocked;       // blocked restart intervals in 'analyze'
    long unforced;      // not forced (slow glue > fast glue)
    long forced;        // forced (slow glue < fast glue)
    long reused;        // number of time trail was (partially) reused
  } restart;

  long reports, sections;

  long bumped;                  // seen and bumped variables in 'analyze'
  long resolved;                // resolved redundant clauses in 'analyze'
  long searched;                // searched decisions in 'decide'

  struct { long count, clauses, bytes; } reduce; // in 'reduce'
  struct { long learned, minimized; } literals;  // in 'minimize_clause'

  struct { long redundant, irredundant, current, max; } clauses;
  struct { struct { size_t current, max; } total, watcher; } bytes;

  struct { long unit, binary; } learned;

  int fixed;                    // top level assigned variables

  Stats ();
  void print (Solver &);
};

};

#endif
