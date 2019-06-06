#ifndef _limit_hpp_INCLUDED
#define _limit_hpp_INCLUDED

namespace CaDiCaL {

struct Limit {

  bool initialized;

  long conflicts;       // conflict limit if non-negative
  long decisions;       // decision limit if non-negative
  long preprocessing;   // limit on preprocessing rounds
  long localsearch;     // limit on local search rounds

  long compact;         // conflict limit for next 'compact'
  long elim;            // conflict limit for next 'elim'
  long flush;           // conflict limit for next 'flush'
  long probe;           // conflict limit for next 'probe'
  long reduce;          // conflict limit for next 'reduce'
  long rephase;         // conflict limit for next 'rephase'
  long report;          // report limit for header
  long restart;         // conflict limit for next 'restart'
  long stabilize;       // conflict limit for next 'stabilize'
  long subsume;         // conflict limit for next 'subsume'

  int keptsize;         // maximum kept size in 'reduce'
  int keptglue;         // maximum kept glue in 'reduce'

  // How often rephased during (1) or out (0) of stabilization.
  //
  long rephased[2];

  // Current elimination bound per eliminated variable.
  //
  long elimbound;

  Limit ();
};

struct Last {
  struct { long propagations; } transred, vivify;
  struct { long fixed, subsumephases, marked; } elim;
  struct { long propagations, reductions; } probe;
  struct { long conflicts; } reduce, rephase;
  struct { long marked; } ternary;
  struct { long fixed; } collect;
  Last ();
};

struct Inc {
  long flush;           // flushing interval in terms of conflicts
  long stabilize;       // stabilization interval increment
  long conflicts;       // next conflict limit if non-negative
  long decisions;       // next decision limit if non-negative
  long preprocessing;   // next preprocessing limit if non-negative
  long localsearch;     // next local search limit if non-negative
  Inc ();
};

}

#endif
