#ifndef _stats_hpp_INCLUDED
#define _stats_hpp_INCLUDED


#include <cstdlib>

namespace CaDiCaL {

class Internal;

struct Stats {

  Internal * internal;

  long conflicts;    // generated conflicts in 'propagate'
  long decisions;    // number of decisions in 'decide'

  struct {
    long probe;      // propagated during probing
    long search;     // propagated literals during search
    long vivify;     // propagated during vivification
    long transred;   // propagated during transitive reduction
  } propagations;

  long compacts;     // number of compactifications
  long rephased;     // actual number of happened rephases
  long restarts;     // actual number of happened restarts
  long reused;       // number of reused trails
  long reports;      // 'report' counter
  long sections;     // 'section' counter
  long added;        // irredundant clauses
  long removed;      // literals in likely to be kept clauses
  long bumped;       // seen and bumped variables in 'analyze'
  long bumplast;     // bumped variables on last decision level
  long searched;     // searched decisions in 'decide'
  long reductions;   // 'reduce' counter
  long reduced;      // number of reduced clauses
  long collected;    // number of collected bytes
  long collections;  // number of garbage collections
  long hbrs;         // hyper binary resolvents
  long hbrsizes;     // sum of hyper resolved base clauses
  long hbreds;       // redundant hyper binary resolvents
  long hbrsubs;      // subsuming hyper binary resolvents
  long subsumed;     // number of subsumed clauses
  long duplicated;   // number of duplicated binary clauses
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
  long decompositions; // number of SCC + ELS
  long vivifications;  // number of vivifications
  long vivifychecks; // checked clauses during vivification
  long vivifydecs;   // vivification decisions
  long vivifyreused; // reused vivification decisions
  long vivifysched;  // scheduled clauses for vivification
  long vivifysubs;   // subsumed clauses during vivification
  long vivifystrs;   // strengthened clauses during vivification
  long vivifyunits;  // units during vivification
  long transreds;
  long transitive;
  long learned;      // learned literals
  long minimized;    // minimized literals
  long redundant;    // number of current redundant clauses
  long irredundant;  // number of current irredundant clauses
  long irrbytes;     // bytes of irredundant clauses
  long original;     // number of original irredundant clauses
  long garbage;      // bytes current irredundant garbage clauses
  long units;        // learned unit clauses
  long binaries;     // learned binary clauses
  long probings;     // number of probings
  long probed;       // number of probed literals
  long failed;       // number of failed literals
#ifdef STATS
  long visits;       // visited clauses in propagation
  long traversed;    // traversed literals in propagation
#endif

  struct {
    int fixed;         // number of top level assigned variables
    int eliminated;    // number of eliminated variables
    int substituted;   // number of substituted variables
  } all, now;

  Stats ();

  void print (Internal *);
};

/*------------------------------------------------------------------------*/

#ifdef STATS
#define EXPENSIVE_STATS_ADD(STAT,INC) \
do { \
  stats.STAT += (INC); \
} while (0)
#else
#define EXPENSIVE_STATS_ADD(STAT,INC) do { } while (0)
#endif

/*------------------------------------------------------------------------*/

};

#endif
