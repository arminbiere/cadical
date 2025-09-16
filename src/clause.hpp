#ifndef _clause_hpp_INCLUDED
#define _clause_hpp_INCLUDED

#include "util.hpp"
#include <climits>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <sys/types.h>
#include <inttypes.h>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

typedef int *literal_iterator;
typedef const int *const_literal_iterator;

/*------------------------------------------------------------------------*/

// The 'Clause' data structure is very important. There are usually many
// clauses and accessing them is a hot-spot.  Thus we use common
// optimizations to reduce memory and improve cache usage, even though this
// induces some complexity in understanding the code.
//
// The most important optimization is to 'embed' the actual literals in the
// clause.  This requires a variadic size structure and thus strictly is not
// 'C' conform, but supported by all compilers we used.  The alternative is
// to store the actual literals somewhere else, which not only needs more
// memory but more importantly also requires another memory access and thus
// is very costly.

#define USED_SIZE 5
#define GLUE_SIZE 12
#define MAX_GLUE (unsigned)((1<<GLUE_SIZE) - 1)
#define SWEPT(c) (c)->temporary_mark
#define ENQUEUED(c) (c)->temporary_mark
#define FROZEN(c) (c)->temporary_mark

struct Clause {
#ifndef NDEBUG
  union {
    int64_t raw_id;   // Used to create LRAT-style proofs
    Clause *copy_ptr; // Only valid if 'moved', then that's where to.
    //
    // The 'copy' field is only valid for 'moved' clauses in the moving
    // garbage collector 'copy_non_garbage_clauses' for keeping clauses
    // compactly in a contiguous memory arena.  Otherwise, so almost all of
    // the time, 'id' is valid.  See 'collect.cpp' for details.
  };
#endif
  uint32_t id_lower_bits;
  uint32_t id_higher_bits;
  unsigned used : USED_SIZE; // resolved in conflict analysis since last
                             // 'reduce'
  bool conditioned : 1; // Tried for globally blocked clause elimination.
  bool covered : 1;  // leftovers from the last covered clause elimination.
  bool garbage : 1;  // can be garbage collected unless it is a 'reason'
  bool gate : 1;     // Clause part of a gate (function definition), used in elimination
  bool hyper : 1;    // redundant hyper binary or ternary resolved
  bool instantiated : 1; // tried to instantiate
  bool moved : 1;        // moved during garbage collector ('copy' valid)
  bool reason : 1;       // reason / antecedent clause can not be collected
  bool redundant : 1;    // aka 'learned' so not 'irredundant' (original)
  bool transred : 1;     // leftovers from the last transitive reduction
  bool subsume : 1;      // leftovers from the last subsumption round
  bool flushed : 1;      // garbage in proof deleted binaries
  bool vivified : 1; // clause already vivified
  bool vivify : 1;   // leftovers from the last vivification
  bool temporary_mark : 1; // used for markings for once inprocessing
  // technique if also removed at the end

  // The glucose level ('LBD' or short 'glue') is a heuristic value for the
  // expected usefulness of a learned clause, where smaller glue is consider
  // more useful.  During learning the 'glue' is determined as the number of
  // decisions in the learned clause.  Thus the glue of a clause is a strict
  // upper limit on the smallest number of decisions needed to make it
  // propagate.  For instance a binary clause will propagate if one of its
  // literals is set to false.  Similarly a learned clause with glue 1 can
  // propagate after one decision, one with glue 2 after 2 decisions etc.
  // In some sense the glue is an abstraction of the size of the clause.
  //
  // See the IJCAI'09 paper by Audemard & Simon for more details.  We
  // switched back and forth between keeping the glue stored in a clause and
  // using it only initially to determine whether it is kept, that is
  // survives clause reduction.  The latter strategy is not bad but also
  // does not allow to use glue values for instance in 'reduce'.
  //
  // More recently we also update the glue and promote clauses to lower
  // level tiers during conflict analysis.  The idea of using three tiers is
  // also due to Chanseok Oh and thus used in all recent 'Maple...' solvers.
  // Tier one are the always kept clauses with low glue at most
  // 'opts.reducetier1glue' (default '2'). The second tier contains all
  // clauses with glue larger than 'opts.reducetier1glue' but smaller or
  // equal than 'opts.reducetier2glue' (default '6').  The third tier
  // consists of clauses with glue larger than 'opts.reducetier2glue'.
  //
  // Clauses in tier one are not deleted in 'reduce'. Clauses in tier
  // two require to be unused in two consecutive 'reduce' intervals before
  // being collected while for clauses in tier three not being used since
  // the last 'reduce' call makes them deletion candidates.  Clauses derived
  // by hyper binary or ternary resolution (even though small and thus with
  // low glue) are always removed if they remain unused during one interval.
  // See 'mark_useless_redundant_clauses_as_garbage' in 'reduce.cpp' and
  // 'bump_clause' in 'analyze.cpp'.
  //
  unsigned glue : GLUE_SIZE;

  int size; // Actual size of 'literals' (at least 2).
  int pos;  // Position of last watch replacement [Gent'13].

  // This 'flexible array member' is of variadic 'size' (and actually
  // shrunken if strengthened) and keeps the literals close to the header of
  // the clause to avoid another pointer dereference, which would be costly.

  // In earlier versions we used 'literals[2]' to fake it (in order to
  // support older Microsoft compilers even though this feature is in C99)
  // and at the same time being able to overlay the first two literals with
  // the 'copy' field above, as having a flexible array member inside a
  // union is not allowed.  Now compilers start to figure out that those
  // literals can be accessed with indices larger than 1 and produce
  // warnings.  After having the 'id' field mandatory we now overlay that
  // one with the copy field.

  // However, it turns out that even though flexible array members are in
  // C99 they are not in C11++, and therefore pedantic compilation with
  // '--pedantic' fails completely. Therefore we still support as
  // alternative faked flexible array members, which unfortunately need
  // then again more care when accessing the literals outside the faked
  // virtual sizes and the compiler can somehow figure that out, because
  // that would in turn produce a warning.

#ifndef NFLEXIBLE
  int literals[];
#else
  int literals[2];
#endif

  // Supports simple range based for loops over clauses.

  literal_iterator begin () { return literals; }
  literal_iterator end () { return literals + size; }

  const_literal_iterator begin () const { return literals; }
  const_literal_iterator end () const { return literals + size; }

  static size_t bytes (int size) {

    // Memory sanitizer insists that clauses put into consecutive memory in
    // the arena are still 4 byte aligned.  We could also allocate 8 byte
    // aligned memory there.  However, assuming the real memory foot print
    // of a clause is 4 bytes anyhow, we just allocate 4 byte aligned memory
    // all the time (even if allocated outside of the arena).
    //
    assert (size > 1);
    const size_t header_bytes = sizeof (Clause);
    const size_t actual_literal_bytes = size * sizeof (int);
    size_t combined_bytes = header_bytes + actual_literal_bytes;
#ifdef NFLEXIBLE
    const size_t faked_literals_bytes = sizeof ((Clause *) 0)->literals;
    combined_bytes -= faked_literals_bytes;
#endif
    size_t aligned_bytes = align (combined_bytes, 4);
    return aligned_bytes;
  }

  size_t bytes () const { return bytes (size); }

  // Check whether this clause is ready to be collected and deleted.  The
  // 'reason' flag is only there to protect reason clauses in 'reduce',
  // which does not backtrack to the root level.  If garbage collection is
  // triggered from a preprocessor, which backtracks to the root level, then
  // 'reason' is false for sure. We want to use the same garbage collection
  // code though for both situations and thus hide here this variance.
  //
  bool collect () const { return !reason && garbage; }
  Clause *copy () const {
    assert (moved);
    const uint32_t lower_bits = (uint32_t) literals[0];
    const uint32_t higher_bits = (uint32_t) literals[1];
    Clause *p =
      (Clause *) ((((uint64_t)higher_bits) << 32) + (uint64_t)lower_bits);
    assert (p == copy_ptr);
    return p;
  };
  void set_copy (Clause *c) {
#ifndef NDEBUG
    copy_ptr = c;
#endif
    size_t addr = (size_t) c;
    const uint32_t lower_bits = static_cast <uint32_t> (addr);
    const uint32_t higher_bits = static_cast <uint32_t> (addr >> 32);
    literals[0] = (int) lower_bits;
    literals[1] = (int) higher_bits;
    assert (copy () == c);
  }
  int64_t lrat_id () const {
    // assert (!moved); // used in collect () even if meaningless (!)
    const uint32_t lower_bits = (uint32_t) id_lower_bits;
    const uint32_t higher_bits = (uint32_t) id_higher_bits;
    int64_t p = ((((uint64_t)higher_bits) << 32) + (uint64_t)lower_bits);
    return p;
  }
  void set_lrat_id (int64_t id) {
    assert (!moved);
#ifndef NDEBUG
    raw_id = id;
#endif
    const unsigned lower_bits = static_cast <uint32_t> (id);
    const unsigned higher_bits = id >> 32;
    id_lower_bits = lower_bits;
    id_higher_bits = higher_bits;
    assert (moved || lrat_id () == raw_id);
  }
};

struct clause_smaller_size {
  bool operator() (const Clause *a, const Clause *b) {
    return a->size < b->size;
  }
};

/*------------------------------------------------------------------------*/

// Place literals over the same variable close to each other.  This would
// allow eager removal of identical literals and detection of tautological
// clauses but is only currently used for better logging (see also
// 'opts.logsort' in 'logging.cpp').

struct clause_lit_less_than {
  bool operator() (int a, int b) const {
    using namespace std;
    int s = abs (a), t = abs (b);
    return s < t || (s == t && a < b);
  }
};

} // namespace CaDiCaL

#endif
