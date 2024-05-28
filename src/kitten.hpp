#ifndef _kitten_hpp_INCLUDED
#define _kitten_hpp_INCLUDED

#include <cstdint>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// This implements the 'kitten' solver of kissat (TODO see paper? or
// kissat source code)
// It is used for ...
// TODO can be used as a standalone solver?

/*------------------------------------------------------------------------*/

typedef struct Kar Kar;
typedef struct Kink Kink;
typedef struct Klause Klause;
typedef struct Katch Katch;
typedef struct Kimits Kimits;
// typedef STACK (unsigned) klauses;
// typedef STACK (katch) katches;

struct Kar {
  unsigned level;
  unsigned reason;
};

struct Klause {
  unsigned aux;
  unsigned size;
  unsigned flags;
  unsigned literals[1];
};

struct Katch {
  unsigned ref;
};

struct Kink {
  unsigned next;
  unsigned prev;
  uint64_t stamp;
}

struct Kimits {
  uint64_t ticks;
}

typedef vector<Katch>
    Katcher;

/*------------------------------------------------------------------------*/

class Kitten {

  Internal *internal;

  // convert to internal (kitten) representation of literals as unsigned
  unsigned int2u (int lit) {
    int idx = abs (lit);
    return (lit < 0) + 2u * (unsigned) idx;
  }

  // internal representation of literals as unsigned
  int u2int (unsigned ulit) {
    int res = u / 2;
    if (u & 1)
      res = -res;
    return res;
  }

  struct {

    uint64_t learned;      // number of
    uint64_t original;     // number of
    uint64_t flip;         // number of
    uint64_t flipped;      // number of
    uint64_t sat;          // number of
    uint64_t solve;        // number of
    uint64_t solved;       // number of
    uint64_t conflicts;    // number of
    uint64_t decisions;    // number of
    uint64_t propagations; // number of
    uint64_t ticks;        // number of
    uint64_t unknown;      // number of
    uint64_t unsat;        // number of

  } stats;

public:
  Kitten (Internal *);
  ~Kitten ();

  void init ();
  void clear ();
  void release ();

  void track_antecedents ();
  void shuffle_clauses ();
  void flip_phases ();

  void assume (int lit);

  void clause (vector<int> &) // const?
      void unit (int);
  void binary (int, int);

  void clause_with_id_and_exception (uint64_t id, const vector<int> &,
                                     unsigned except);

  void no_ticks_limit ();
  void set_ticks_limit (uint64_t);

  void solve ();
  void status ();

  signed char value (int);
  signed char fixed (int);
  bool failed (int);
  bool flip_literal (unsigned);

  int compute_clausal_core (vector<uint64_t>); // args?
  void shrink_to_clausal_core ();

  void traverse_core_ids (); // args?

  void traverse_core_clauses (); // args?
};

} // namespace CaDiCaL

#endif
