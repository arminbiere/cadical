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
  long probagations; // propagated during 'probe'
  long restarts;     // actual number of happened restarts
  long reused;       // number of reused trails
  long reports;      // 'report' counter
  long sections;     // 'section' counter
  long added;        // irredundant clauses
  long removed;      // literals in likely to be kept clauses
  long bumped;       // seen and bumped variables in 'analyze'
  long bumplast;     // bumped variables on last decision level
  long trailbumped;  // bumped 'reverse' instead of 'earlier'
  long analyzed;     // analyzed redundant clauses
  long searched;     // searched decisions in 'decide'
  long reductions;   // 'reduce' counter
  long reduced;      // number of reduced clauses
  long collected;    // number of collected bytes
  long collections;  // number of garbage collections
#ifdef SHRINK
  long shrunken;     // removed literals in learned clauses
  long shrinktried;  // number of tried to shrink literals
#endif
#ifdef BACKWARD
  long sublast;      // number of eagerly subsumed clauses
#endif
  long subsumed;     // number of subsumed clauses
#ifdef BCE
  long blockings;    // blocked clause elimination rounds
  long blocked;      // number of blocked clauses
  long blockres;     // number of resolved clauses in BCE
  long blockres2;    // number of resolved binary clauses in BCE
  long blocktried;   // number of tried clauses in BCE
  long redblocked;   // number of blocked redundant clauses
#endif
  long strengthened; // number of strengthened clauses
  long subirr;       // number of subsumed irredundant clauses
  long subred;       // number of subsumed redundant clauses
  long subtried;     // number of tried subsumptions
  long subchecks;    // number of pair-wise subsumption checks
  long subchecks2;   // same but restricted to binary clauses
  long subsumptions; // number of subsumption phases
  long elimres;      // number of resolved clauses in BVE
  long elimres2;     // number of resolved binary clauses in BVE
  long elimrestried; // number of tried resolved clauses in BVE
  long eliminations; // number of elimination phases
  long learned;      // learned literals
  long minimized;    // minimized literals
  long redundant;    // number of current redundant clauses
  long irredundant;  // number of current irredundant clauses
  long irrbytes;     // bytes of irredundant clauses
  long original;     // number of original irredundant clauses
  long garbage;      // bytes of current garbage clauses
  long units;        // learned unit clauses
  long binaries;     // learned binary clauses
  long probings;     // number of probings
  long probed;       // number of probed literals
  long failed;       // number of failed literals
#ifdef STATS
  long visits;       // visited clauses in propagation
  long traversed;    // traversed literals in propagation
#endif

  int fixed;         // number of top level assigned variables
  int eliminated;    // number of eliminated variables

  Stats ();
  void print (Internal *);
};

/*------------------------------------------------------------------------*/

#ifdef STATS
#define EXPENSIVE_STATS_ADD(COND,STAT,INC) \
do { \
  if (!(COND)) break; \
  stats.STAT += (INC); \
} while (0)
#else
#define EXPENSIVE_STATS_ADD(COND,STAT,INC) do { } while (0)
#endif

/*------------------------------------------------------------------------*/

};

#endif
