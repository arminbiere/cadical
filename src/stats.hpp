#ifndef _stats_hpp_INCLUDED
#define _stats_hpp_INCLUDED

#include <cstdlib>

namespace CaDiCaL {

struct Internal;

struct Stats {

  Internal * internal;

  long vars;         // internal initialized variables

  long conflicts;    // generated conflicts in 'propagate'
  long decisions;    // number of decisions in 'decide'

  struct {
    long cover;      // propagated during covered clause elimination
    long instantiate;// propagated during variable instantiation
    long probe;      // propagated during probing
    long search;     // propagated literals during search
    long transred;   // propagated during transitive reduction
    long vivify;     // propagated during vivification
    long walk;       // propagated during local search
  } propagations;

  struct {
    long block;      // block marked literals
    long elim;       // elim marked variables
    long subsume;    // subsume marked variables
    long ternary;    // ternary marked variables
  } mark;

  struct {
    long total;
    long redundant;
    long irredundant;
  } current, added;  // Clauses.

  struct { double process, real; } time;

  struct {
    long count;      // number of covered clause elimination rounds
    long asymmetric; // number of asymmetric tautologies in CCE
    long blocked;    // number of blocked covered tautologies
    long total;      // total number of eliminated clauses
  } cover;

  struct {
    long tried;
    long succeeded;
    struct { long one, zero; } constant, forward, backward;
    struct { long positive, negative; } horn;
  } lucky;

  struct {
    long total;      // total number of happened rephases
    long best;       // how often reset to best phases
    long flipped;    // how often reset phases by flipping
    long inverted;   // how often reset to inverted phases
    long original;   // how often reset to original phases
    long random;     // how often randomly reset phases
    long walk;       // phases improved through random walked
  } rephased;

  struct {
    long count;
    long broken;
    long flips;
    long minimum;
  } walk;

  struct {
    long count;      // flushings of learned clauses counter
    long learned;    // flushed learned clauses
    long hyper;      // flushed hyper binary/ternary clauses
  } flush;

  long compacts;     // number of compactifications
  long shuffled;     // shuffled queues and scores
  long restarts;     // actual number of happened restarts
  long restartlevels;// levels at restart
  long restartstable;// actual number of happened restarts
  long stabphases;   // number of stabilization phases
  long stabconflicts;// number of search conflicts during stabilizing
  long rescored;     // number of times scores were rescored
  long reused;       // number of reused trails
  long reusedlevels; // reused levels at restart
  long reusedstable; // number of reused trails during stabilizing
  long sections;     // 'section' counter
  long chrono;       // chronological backtracks
  long backtracks;   // number of backtracks
  long bumped;       // seen and bumped variables in 'analyze'
  long searched;     // searched decisions in 'decide'
  long reductions;   // 'reduce' counter
  long reduced;      // number of reduced clauses
  long collected;    // number of collected bytes
  long collections;  // number of garbage collections
  long hbrs;         // hyper binary resolvents
  long hbrsizes;     // sum of hyper resolved base clauses
  long hbreds;       // redundant hyper binary resolvents
  long hbrsubs;      // subsuming hyper binary resolvents
  long instried;     // number of tried instantiations
  long instantiated; // number of successful instantiations
  long instrounds;   // number of instantiation rounds
  long subsumed;     // number of subsumed clauses
  long deduplicated; // number of removed duplicated binary clauses
  long deduplications;//number of deduplication phases
  long strengthened; // number of strengthened clauses
  long elimotfstr;   // number of on-the-fly strengthened during elimination
  long subirr;       // number of subsumed irredundant clauses
  long subred;       // number of subsumed redundant clauses
  long subtried;     // number of tried subsumptions
  long subchecks;    // number of pair-wise subsumption checks
  long subchecks2;   // same but restricted to binary clauses
  long elimotfsub;   // number of on-the-fly subsumed during elimination
  long subsumerounds;// number of subsumption rounds
  long subsumephases;// number of scheduled subsumption phases
  long eagertried;   // number of traversed eager subsumed candidates
  long eagersub;     // number of eagerly subsumed recently learned clauses
  long elimres;      // number of resolved clauses in BVE
  long elimrestried; // number of tried resolved clauses in BVE
  long elimrounds;   // number of elimination rounds
  long elimphases;   // number of scheduled elimination phases
  long elimcompleted;// number complete elimination procedures
  long elimtried;    // number of variable elimination attempts
  long elimsubst;    // number of eliminations through substitutions
  long elimgates;    // number of gates found during elimination
  long elimequivs;   // number of equivalences found during elimination
  long elimands;     // number of AND gates found during elimination
  long elimites;     // number of ITE gates found during elimination
  long elimxors;     // number of XOR gates found during elimination
  long elimbwsub;    // number of eager backward subsumed clauses
  long elimbwstr;    // number of eager backward strengthened clauses
  long ternary;      // number of ternary resolution phases
  long ternres;      // number of ternary resolutions
  long htrs;         // number of hyper ternary resolvents
  long htrs2;        // number of binary hyper ternary resolvents
  long htrs3;        // number of ternary hyper ternary resolvents
  long decompositions; // number of SCC + ELS
  long vivifications;  // number of vivifications
  long vivifychecks; // checked clauses during vivification
  long vivifydecs;   // vivification decisions
  long vivifyreused; // reused vivification decisions
  long vivifysched;  // scheduled clauses for vivification
  long vivifysubs;   // subsumed clauses during vivification
  long vivifystrs;   // strengthened clauses during vivification
  long vivifystrirr; // strengthened irredundant clause
  long vivifystred1; // strengthened redundant clause (1)
  long vivifystred2; // strengthened redundant clause (2)
  long vivifystred3; // strengthened redundant clause (3)
  long vivifyunits;  // units during vivification
  long transreds;
  long transitive;
  struct {
    long literals;
    long clauses;
  } learned;
  long minimized;    // minimized literals
  long irrbytes;     // bytes of irredundant clauses
  long garbage;      // bytes current irredundant garbage clauses
  long units;        // learned unit clauses
  long binaries;     // learned binary clauses
  long probingphases;// number of scheduled probing phases
  long probingrounds;// number of probing rounds
  long probed;       // number of probed literals
  long failed;       // number of failed literals
  long hyperunary;   // hyper unary resolved unit clauses
  long probefailed;  // failed literals from probing
  long transredunits;// units derived in transitive reduction
  long blockings;    // number of blocked clause eliminations
  long blocked;      // number of actually blocked clauses
  long blockres;     // number of resolutions during blocking
  long blockcands;   // number of clause / pivot pairs tried
  long blockpured;   // number of clauses blocked through pure literals
  long blockpurelits;// number of pure literals
  long extensions;   // number of extended witnesses
  long extended;     // number of flipped literals during extension
  long weakened;     // number of clauses pushed to extension stack
  long weakenedlen;  // lengths of weakened clauses
  long restorations; // number of restore calls
  long restored;     // number of restored clauses
  long reactivated;  // number of reactivated clauses
  long restoredlits; // number of restored literals

  long preprocessings;
  struct {
    int fixed;       // number of top level assigned variables
    int eliminated;  // number of eliminated variables
    int substituted; // number of substituted variables
    int pure;        // number of pure literals
  } all, now;

  int unused;        // number of unused variables
  int active;        // number of active variables
  int inactive;      // number of inactive variables

  Stats ();

  void print (Internal *);
};

/*------------------------------------------------------------------------*/

}

#endif
