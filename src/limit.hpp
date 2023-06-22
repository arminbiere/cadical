#ifndef _limit_hpp_INCLUDED
#define _limit_hpp_INCLUDED

namespace CaDiCaL {

struct Limit {

  bool initialized;

  int64_t conflicts;     // conflict limit if non-negative
  int64_t decisions;     // decision limit if non-negative
  int64_t preprocessing; // limit on preprocessing rounds
  int64_t localsearch;   // limit on local search rounds

  int64_t compact;   // conflict limit for next 'compact'
  int64_t condition; // conflict limit for next 'condition'
  int64_t elim;      // conflict limit for next 'elim'
  int64_t flush;     // conflict limit for next 'flush'
  int64_t probe;     // conflict limit for next 'probe'
  int64_t reduce;    // conflict limit for next 'reduce'
  int64_t rephase;   // conflict limit for next 'rephase'
  int64_t report;    // report limit for header
  int64_t restart;   // conflict limit for next 'restart'
  int64_t stabilize; // conflict limit for next 'stabilize'
  int64_t subsume;   // conflict limit for next 'subsume'

  int keptsize; // maximum kept size in 'reduce'
  int keptglue; // maximum kept glue in 'reduce'

  // How often rephased during (1) or out (0) of stabilization.
  //
  int64_t rephased[2];

  // Current elimination bound per eliminated variable.
  //
  int64_t elimbound;

  struct {
    int check;  // countdown to next terminator call
    int forced; // forced termination for testing
  } terminate;

  Limit ();
};

struct Last {
  struct {
    int64_t propagations;
  } transred, vivify;
  struct {
    int64_t fixed, subsumephases, marked;
  } elim;
  struct {
    int64_t propagations, reductions;
  } probe;
  struct {
    int64_t conflicts;
  } reduce, rephase;
  struct {
    int64_t marked;
  } ternary;
  struct {
    int64_t fixed;
  } collect;
  Last ();
};

struct Inc {
  int64_t flush;         // flushing interval in terms of conflicts
  int64_t stabilize;     // stabilization interval increment
  int64_t conflicts;     // next conflict limit if non-negative
  int64_t decisions;     // next decision limit if non-negative
  int64_t preprocessing; // next preprocessing limit if non-negative
  int64_t localsearch;   // next local search limit if non-negative
  Inc ();
};

} // namespace CaDiCaL

#endif
