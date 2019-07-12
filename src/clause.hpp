#ifndef _clause_hpp_INCLUDED
#define _clause_hpp_INCLUDED

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

typedef       int *       literal_iterator;
typedef const int * const_literal_iterator;

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

struct Clause {
#ifdef LOGGING
  int64_t id;         // Only useful for debugging.
#endif
  bool covered:1;     // Already considered for covered clause elimination.
  bool enqueued:1;    // Enqueued on backward queue.
  bool frozen:1;      // Temporarily frozen (in covered clause elimination).
  bool garbage:1;     // can be garbage collected unless it is a 'reason'
  bool gate:1 ;       // Clause part of a gate (function definition).
  bool hyper:1;       // redundant hyper binary or ternary resolved
  bool instantiated:1;// tried to instantiate
  bool keep:1;        // always keep this clause (if redundant)
  bool moved:1;       // moved during garbage collector ('copy' valid)
  bool reason:1;      // reason / antecedent clause can not be collected
  bool redundant:1;   // aka 'learned' so not 'irredundant' (original)
  bool transred:1;    // already checked for transitive reduction
  bool subsume:1;     // not checked in last subsumption round
  bool used:1;        // resolved in conflict analysis since last 'reduce'
  bool vivified:1;    // clause already vivified
  bool vivify:1;      // clause scheduled to be vivified

  // The glucose level ('LBD' or short 'glue') is a heuristic value for the
  // expected usefulness of a learned clause, where smaller glue is consider
  // more useful.  During learning the 'glue' is determined as the number of
  // decisions in the learned clause.  Thus the glue of a clause is a strict
  // upper limit on the smallest number of decisions needed to make it
  // propagate.  For instance a binary clause will propagate if one of its
  // literals is set to false.  Similarly a learned clause with glue 2 can
  // propagate after one decision, one with glue 3 after 2 decisions etc.
  // In some sense the glue is an abstraction of the size of the clause.
  //
  // See the IJCAI'09 paper by Audemard & Simon for more details.  We
  // switched back and forth between keeping the glue stored in a clause and
  // using it only initially to determine whether it is kept, that is
  // survives clause reduction.  The latter strategy is not bad but also
  // does not allow to use glue values for instance in 'reduce'.
  //
  int glue;

  int size;         // actual size of 'literals' (at least 2)
  int pos;          // position of last watch replacement

  union {

    int literals[2];    // of variadic 'size' (not just 2) in general

    Clause * copy;      // only valid if 'moved', then that's where to
    //
    // The 'copy' field is only valid for 'moved' clauses in the moving
    // garbage collector 'copy_non_garbage_clauses' for keeping clauses
    // compactly in a contiguous memory arena.  Otherwise, that is most of
    // the time, 'literals' is valid.  See 'collect.cpp' for details.
  };

  literal_iterator       begin ()       { return literals; }
  literal_iterator         end ()       { return literals + size; }

  const_literal_iterator begin () const { return literals; }
  const_literal_iterator   end () const { return literals + size; }

  size_t bytes () const { return (size - 2) * sizeof (int) + sizeof *this; }

  // Check whether this clause is ready to be collected and deleted.  The
  // 'reason' flag is only there to protect reason clauses in 'reduce',
  // which does not backtrack to the root level.  If garbage collection is
  // triggered from a preprocessor, which backtracks to the root level, then
  // 'reason' is false for sure. We want to use the same garbage collection
  // code though for both situations and thus hide here this variance.
  //
  bool collect () const { return !reason && garbage; }
};

struct clause_smaller_size {
  bool operator () (const Clause * a, const Clause * b) {
    return a->size < b->size;
  }
};

/*------------------------------------------------------------------------*/

// Place literals over the same variable close to each other.  This would
// allow eager removal of identical literals and detection of tautological
// clauses but is only currently used for better logging (see also
// 'opts.logsort' in 'logging.cpp').

struct clause_lit_less_than {
  bool operator () (int a, int b) const {
    int s = abs (a), t = abs (b);
    return s < t || (s == t && a < b);
  }
};

}

#endif
