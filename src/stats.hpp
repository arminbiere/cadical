#ifndef _stats_hpp_INCLUDED
#define _stats_hpp_INCLUDED

#include <cstdlib>

namespace CaDiCaL {

struct Internal;

struct Stats {

  Internal * internal;

  int64_t vars;         // internal initialized variables

  int64_t conflicts;    // generated conflicts in 'propagate'
  int64_t decisions;    // number of decisions in 'decide'

  struct {
    int64_t cover;      // propagated during covered clause elimination
    int64_t instantiate;// propagated during variable instantiation
    int64_t probe;      // propagated during probing
    int64_t search;     // propagated literals during search
    int64_t transred;   // propagated during transitive reduction
    int64_t vivify;     // propagated during vivification
    int64_t walk;       // propagated during local search
  } propagations;

  int64_t condassinit;  // initial assigned literals
  int64_t condassirem;  // initial assigned literals for blocked
  int64_t condassrem;   // remaining assigned literals for blocked
  int64_t condassvars;  // sum of active variables at initial assignment
  int64_t condautinit;  // initial literals in autarky part
  int64_t condautrem;   // remaining literals in autarky part for blocked
  int64_t condcands;    // globally blocked candidate clauses
  int64_t condcondinit; // initial literals in conditional part
  int64_t condcondrem;  // remaining literals in conditional part for blocked
  int64_t conditioned;  // globally blocked clauses eliminated
  int64_t conditionings;// globally blocked clause eliminations
  int64_t condprops;    // propagated unassigned literals

  struct {
    int64_t block;      // block marked literals
    int64_t elim;       // elim marked variables
    int64_t subsume;    // subsume marked variables
    int64_t ternary;    // ternary marked variables
  } mark;

  struct {
    int64_t total;
    int64_t redundant;
    int64_t irredundant;
  } current, added;  // Clauses.

  struct { double process, real; } time;

  struct {
    int64_t count;      // number of covered clause elimination rounds
    int64_t asymmetric; // number of asymmetric tautologies in CCE
    int64_t blocked;    // number of blocked covered tautologies
    int64_t total;      // total number of eliminated clauses
  } cover;

  struct {
    int64_t tried;
    int64_t succeeded;
    struct { int64_t one, zero; } constant, forward, backward;
    struct { int64_t positive, negative; } horn;
  } lucky;

  struct {
    int64_t total;      // total number of happened rephases
    int64_t best;       // how often reset to best phases
    int64_t flipped;    // how often reset phases by flipping
    int64_t inverted;   // how often reset to inverted phases
    int64_t original;   // how often reset to original phases
    int64_t random;     // how often randomly reset phases
    int64_t walk;       // phases improved through random walked
  } rephased;

  struct {
    int64_t count;
    int64_t broken;
    int64_t flips;
    int64_t minimum;
  } walk;

  struct {
    int64_t count;      // flushings of learned clauses counter
    int64_t learned;    // flushed learned clauses
    int64_t hyper;      // flushed hyper binary/ternary clauses
  } flush;

  int64_t compacts;     // number of compactifications
  int64_t shuffled;     // shuffled queues and scores
  int64_t restarts;     // actual number of happened restarts
  int64_t restartlevels;// levels at restart
  int64_t restartstable;// actual number of happened restarts
  int64_t stabphases;   // number of stabilization phases
  int64_t stabconflicts;// number of search conflicts during stabilizing
  int64_t rescored;     // number of times scores were rescored
  int64_t reused;       // number of reused trails
  int64_t reusedlevels; // reused levels at restart
  int64_t reusedstable; // number of reused trails during stabilizing
  int64_t sections;     // 'section' counter
  int64_t chrono;       // chronological backtracks
  int64_t backtracks;   // number of backtracks
  int64_t improvedglue; // improved glue during bumping
  int64_t promoted1;    // promoted clauses to tier one
  int64_t promoted2;    // promoted clauses to tier two
  int64_t bumped;       // seen and bumped variables in 'analyze'
  int64_t recomputed;   // recomputed glues 'recompute_glue'
  int64_t searched;     // searched decisions in 'decide'
  int64_t reductions;   // 'reduce' counter
  int64_t reduced;      // number of reduced clauses
  int64_t collected;    // number of collected bytes
  int64_t collections;  // number of garbage collections
  int64_t hbrs;         // hyper binary resolvents
  int64_t hbrsizes;     // sum of hyper resolved base clauses
  int64_t hbreds;       // redundant hyper binary resolvents
  int64_t hbrsubs;      // subsuming hyper binary resolvents
  int64_t instried;     // number of tried instantiations
  int64_t instantiated; // number of successful instantiations
  int64_t instrounds;   // number of instantiation rounds
  int64_t subsumed;     // number of subsumed clauses
  int64_t deduplicated; // number of removed duplicated binary clauses
  int64_t deduplications;//number of deduplication phases
  int64_t strengthened; // number of strengthened clauses
  int64_t elimotfstr;   // number of on-the-fly strengthened during elimination
  int64_t subirr;       // number of subsumed irredundant clauses
  int64_t subred;       // number of subsumed redundant clauses
  int64_t subtried;     // number of tried subsumptions
  int64_t subchecks;    // number of pair-wise subsumption checks
  int64_t subchecks2;   // same but restricted to binary clauses
  int64_t elimotfsub;   // number of on-the-fly subsumed during elimination
  int64_t subsumerounds;// number of subsumption rounds
  int64_t subsumephases;// number of scheduled subsumption phases
  int64_t eagertried;   // number of traversed eager subsumed candidates
  int64_t eagersub;     // number of eagerly subsumed recently learned clauses
  int64_t elimres;      // number of resolved clauses in BVE
  int64_t elimrestried; // number of tried resolved clauses in BVE
  int64_t elimrounds;   // number of elimination rounds
  int64_t elimphases;   // number of scheduled elimination phases
  int64_t elimcompleted;// number complete elimination procedures
  int64_t elimtried;    // number of variable elimination attempts
  int64_t elimsubst;    // number of eliminations through substitutions
  int64_t elimgates;    // number of gates found during elimination
  int64_t elimequivs;   // number of equivalences found during elimination
  int64_t elimands;     // number of AND gates found during elimination
  int64_t elimites;     // number of ITE gates found during elimination
  int64_t elimxors;     // number of XOR gates found during elimination
  int64_t elimbwsub;    // number of eager backward subsumed clauses
  int64_t elimbwstr;    // number of eager backward strengthened clauses
  int64_t ternary;      // number of ternary resolution phases
  int64_t ternres;      // number of ternary resolutions
  int64_t htrs;         // number of hyper ternary resolvents
  int64_t htrs2;        // number of binary hyper ternary resolvents
  int64_t htrs3;        // number of ternary hyper ternary resolvents
  int64_t decompositions; // number of SCC + ELS
  int64_t vivifications;  // number of vivifications
  int64_t vivifychecks; // checked clauses during vivification
  int64_t vivifydecs;   // vivification decisions
  int64_t vivifyreused; // reused vivification decisions
  int64_t vivifysched;  // scheduled clauses for vivification
  int64_t vivifysubs;   // subsumed clauses during vivification
  int64_t vivifystrs;   // strengthened clauses during vivification
  int64_t vivifystrirr; // strengthened irredundant clause
  int64_t vivifystred1; // strengthened redundant clause (1)
  int64_t vivifystred2; // strengthened redundant clause (2)
  int64_t vivifystred3; // strengthened redundant clause (3)
  int64_t vivifyunits;  // units during vivification
  int64_t transreds;
  int64_t transitive;
  struct {
    int64_t literals;
    int64_t clauses;
  } learned;
  int64_t minimized; // minimized literals
  int64_t shrunken;  // shrunken literals
  int64_t minishrunken;  // shrunken during minimization literals

  int64_t irrbytes;     // bytes of irredundant clauses
  int64_t garbage;      // bytes current irredundant garbage clauses
  int64_t units;        // learned unit clauses
  int64_t binaries;     // learned binary clauses
  int64_t probingphases;// number of scheduled probing phases
  int64_t probingrounds;// number of probing rounds
  int64_t probesuccess; // number successful probing phases
  int64_t probed;       // number of probed literals
  int64_t failed;       // number of failed literals
  int64_t hyperunary;   // hyper unary resolved unit clauses
  int64_t probefailed;  // failed literals from probing
  int64_t transredunits;// units derived in transitive reduction
  int64_t blockings;    // number of blocked clause eliminations
  int64_t blocked;      // number of actually blocked clauses
  int64_t blockres;     // number of resolutions during blocking
  int64_t blockcands;   // number of clause / pivot pairs tried
  int64_t blockpured;   // number of clauses blocked through pure literals
  int64_t blockpurelits;// number of pure literals
  int64_t extensions;   // number of extended witnesses
  int64_t extended;     // number of flipped literals during extension
  int64_t weakened;     // number of clauses pushed to extension stack
  int64_t weakenedlen;  // lengths of weakened clauses
  int64_t restorations; // number of restore calls
  int64_t restored;     // number of restored clauses
  int64_t reactivated;  // number of reactivated clauses
  int64_t restoredlits; // number of restored literals

  int64_t preprocessings;

  struct {
    int64_t fixed;       // number of top level assigned variables
    int64_t eliminated;  // number of eliminated variables
    int64_t substituted; // number of substituted variables
    int64_t pure;        // number of pure literals
  } all, now;

  int64_t unused;        // number of unused variables
  int64_t active;        // number of active variables
  int64_t inactive;      // number of inactive variables

  Stats ();

  void print (Internal *);
};

/*------------------------------------------------------------------------*/

}

#endif
