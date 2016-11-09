#ifndef _clause_hpp_INCLUDED
#define _clause_hpp_INCLUDED

#include <cstdlib>
#include <cassert>

#include "iterator.hpp"

namespace CaDiCaL {

// The 'Clause' data structure is very important. There are usually many
// clauses and accessing them is a hot-spot.  Thus we use three common
// optimizations to reduce their memory foot print and improve cache usage.
// Even though is induces some complexity in understanding the actual
// implementation, though arguably not the usage of this data-structure,
// we deem these optimizations for essential.
//
//   (1) The most important optimization is to 'embed' the actual literals
//   in the clause.  This requires a variadic size structure and thus
//   strictly is not 'C' conformant, but supported by all compilers we used.
//   The alternative is to store the actual literals somewhere else, which
//   not only needs more memory but more importantly also requires another
//   memory access and thus is so costly that even for CaDiCaL we want to
//   use this optimization.
//
//   (2) The boolean flags only need one bit each and thus there is enough
//   space left to merge them with a 'glue' bit field (which is less
//   accessed than 'size').  This saves 4 bytes and also keeps the header
//   without 'analyzed' nicely in 8 bytes.  We currently use 28 bits and
//   actually since we do not want to mess with 'unsigned' versus 'signed'
//   issues just use 27 out of them.  If more boolean flags are needed this
//   number has to be adapted accordingly.
//
//   (3) Original clauses and clauses with small glue or size are kept
//   anyhow and do not need the activity counter 'analyzed'.  Thus we can
//   omit these 8 bytes used for 'analyzed' for these clauses.  Redundant
//   clauses of long size and with large glue have a 'analyzed' field and
//   are called 'extended'.  The non extended clauses need 8 bytes less and
//   accessing 'analyzed' for them is not allowed.
//
// With these three optimizations a binary original clause only needs 16
// bytes instead of 40 bytes without embedding and 32 bytes with embedding
// the literals.  The last two optimizations reduce memory usage of very
// large formulas slightly but are otherwise not that important.
//
// If you want to add few additional boolean flags, add them after the
// sequence of already existing ones.  This makes sure that these bits and
// the following 'glue' field are put into a 4 byte word by the compiler. Of
// course you need to adapt 'LD_MAX_GLUE' accordingly.  Adding one flag
// reduces it by one.
//
// Similarly if you want to add more data to extended clauses put these
// fields after 'analyzed' and before the flags section.  Then adapt the
// 'EXTENDED_OFFSET' accordingly.
//
// Additional fields needed for all clauses are safely put between 'glue'
// and 'size' without the need to change anything else.  In general these
// optimizations are local to 'clause.[hc]pp' and otherwise can be ignored
// except that you should for instance never access 'analyzed' of a clauses
// which is not extended.  This can be checked with for instance 'valgrind'
// but is also guarded by making the actual '_analyzed' field private and
// checking this contract in the 'analyzed ()' accessors functions.

#define LD_MAX_GLUE     27      // 32 bits - (5 boolean flags)
#define EXTENDED_OFFSET  8      // sizeof (_analyzed)

#define MAX_GLUE ((1<<(LD_MAX_GLUE-1))-1)       // 1 bit less since signed

class Clause {

  long _analyzed;        // time stamp when analyzed last time

public:

  unsigned extended:1;  // 'analyzed' field only valid this is true
  unsigned redundant:1; // aka 'learned' so not 'irredundant' (original)
  unsigned garbage:1;   // can be garbage collected unless it is a 'reason'
  unsigned reason:1;    // reason / antecedent clause can not be collected
  unsigned moved:1;     // moved during garbage collector ('copy' valid)

  // This is the 'glue' = 'glucose level' = 'LBD' of a redundant clause.  We
  // actually only use 'CLAUSE_LD_MAX_GLUE-1' bits since the field is
  // 'signed' to avoid surprises due to 'unsigned' vs. 'signed' semantics.
  //
  // Another issue is that 'C' does not explicitly define 'signedness' of
  // 'int' bit fields and thus we explicitly have to use 'signed' here (on
  // an IBM main frame or on Sparc 'int a:1' might be 'unsigned').
  //
  signed int glue : LD_MAX_GLUE;

  int size;             // actual size of 'literals' (at least 2)
  int pos;

  union {
    int literals[2];    // of variadic 'size' (not just 2) in general
    Clause * copy;      // only valid if 'moved', then that's where

    // The 'copy' field is only used for 'moved' clauses in 'move_clause'
    // in the moving garbage collector 'move_non_garbage_clauses'.
    // Otherwise 'literals' is valid.
  };

  long & analyzed () { assert (extended); return _analyzed; }
  const long & analyzed () const { assert (extended); return _analyzed; }

  literal_iterator       begin ()       { return literals; }
  literal_iterator         end ()       { return literals + size; }
  const_literal_iterator begin () const { return literals; }
  const_literal_iterator   end () const { return literals + size; }

  // Actual start of allocated memory, bytes allocated and offset are only
  // used for memory (de)allocation in 'delete_clause' and in the moving
  // garbage collector 'move_non_garbage_clauses' and 'move_clause'.
  //
  char * start () const;        // actual start of allocated memory
  size_t bytes () const;        // actual number of bytes allocated
  size_t offset () const;       // offset of valid bytes (start - this)

  // Check whether this clause is ready to be collected and deleted.  The
  // 'reason' flag is only there for protecting reason clauses in 'reduce',
  // which does not backtrack to the root level.  If garbage collection is
  // triggered from a preprocessor, which backtracks to the root level, then
  // 'reason' is false for sure. We want to use the same garbage collection
  // code though for both situations and thus hide here this variance.
  //
  bool collect () const { return !reason && garbage; }
};

struct analyzed_earlier {
  bool operator () (const Clause * a, const Clause * b) {
    assert (a->extended), assert (b->extended);
    return a->analyzed () < b->analyzed ();
  }
};

struct smaller_size {
  bool operator () (const Clause * a, const Clause * b) {
    return a->size < b->size;
  }
};

/*------------------------------------------------------------------------*/

inline size_t Clause::bytes () const {
  size_t res = sizeof (Clause) + (size - 2) * sizeof (int);
  if (!extended) res -= sizeof (long);
  return res;
}

inline char * Clause::start () const {
  char * res = (char *) this;
  if (!extended) res += sizeof (long);
  return res;
}

inline size_t Clause::offset () const {
  return extended ? 0 : EXTENDED_OFFSET;
}

};

#endif
