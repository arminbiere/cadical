#ifndef _clause_hpp_INCLUDED
#define _clause_hpp_INCLUDED

#include <cstdlib>
#include <cassert>

#include "iterator.hpp"
#include "util.hpp"

namespace CaDiCaL {

// The 'Clause' data structure is very important. There are usually many
// clauses and accessing them is a hot-spot.  Thus we use three common
// optimizations to reduce their memory foot print and improve cache usage.
// Even though this induces some complexity in understanding the actual
// implementation, arguably not the usage of this data-structure, we
// consider these optimizations as essential.
//
//   (1) The most important optimization is to 'embed' the actual literals
//   in the clause.  This requires a variadic size structure and thus
//   strictly is not 'C' conform, but supported by all compilers we used.
//   The alternative is to store the actual literals somewhere else, which
//   not only needs more memory but more importantly also requires another
//   memory access and thus is very costly.
//
//   (2) The boolean flags only need one bit each and thus there is enough
//   space left to merge them with a 'glue' bit field (which is less
//   accessed than 'size').  This saves 4 bytes and also keeps the header
//   without '_analyzed' and '_pos' nicely in 8 bytes.  We currently use 22
//   bits and, actually, since we do not want to mess with 'unsigned' versus
//   'signed' issues just use 21 out of them.  If more boolean flags are
//   needed this number has to be adapted accordingly.
//
//   (3) Original clauses and clauses with small glue or size are kept
//   anyhow and do not need the activity counter '_analyzed'.  Thus we can
//   omit these 8 bytes used for '_analyzed' for these clauses.  Redundant
//   clauses of long size and with large glue have a '_analyzed' field.
//   The same idea is used for the '_pos' 4 byte integer field which saves
//   the position of the last exchanged watch in a long clause.  However,
//   we always require '_pos' to present if we also need '_analyzed', which
//   is not really an issue, since saving in '_pos' starts making sense for
//   clauses of length 4 and we usually have 'opts.keepsize == 3'.
//
// With these three optimizations a binary clause only needs 16 bytes
// instead of 44 bytes.  The last two optimizations reduce memory usage of
// very large formulas measurably but are otherwise not that important.
//
// If you want to add few additional boolean flags, add them after the
// sequence of already existing ones.  This makes sure that these bits and
// the following 'glue' field are put into a 4 byte word by the compiler. Of
// course you need to adapt 'LD_MAX_GLUE' accordingly.  Adding one flag
// reduces it by one.
//
// Additional fields needed for all clauses are safely put between 'glue'
// and 'size' without the need to change anything else.  In general these
// optimizations are local to 'clause.[hc]pp' and otherwise can be ignored
// except that you should for instance never access 'analyzed' of a clauses
// which is not extended.  This can be checked with for instance 'valgrind'
// but is also guarded by making the actual '_analyzed' field private and
// checking this contract in the 'analyzed ()' accessors functions.

#define LD_MAX_GLUE 22
#define MAX_GLUE ((1 << (LD_MAX_GLUE-1)) - 1)

class Clause {

public:

  long _analyzed;   // time stamp when analyzed last time if redundant
  int _pos;         // position of last watch replacement

  // Keep start of clause and 'copy' field (and thus 'literals[0]' at 64-bit
  // aligned offsets, no matter whether we have an '_analyzed' or '_pos'
  // field.  Otherwise a binary clause does not have 16 bytes.  Keeping
  // clauses at 64-bit aligned addresses gives around 5% speed improvement.
  //
  int dummy;        // unused four bytes alignment

  bool have_analyzed : 1;
  bool have_pos : 1;

  bool redundant:1; // aka 'learned' so not 'irredundant' (original)

  bool garbage:1;   // can be garbage collected unless it is a 'reason'
  bool reason:1;    // reason / antecedent clause can not be collected
  bool moved:1;     // moved during garbage collector ('copy' valid)

  bool hbr:1;	    // redundant hyper binary resolved clause (size == 2)
  bool used:1;      // 'hbr' resolved during conflict analysis

  bool vivify:1;    // irredundant clause scheduled to be vivified
  bool ignore:1;    // ignore during (vivify) propagation

  signed int glue : LD_MAX_GLUE;

  int size;         // actual size of 'literals' (at least 2)

  union {

    int literals[2];    // of variadic 'size' (not just 2) in general

    Clause * copy;      // only valid if 'moved', then that's where to

    // The 'copy' field is only used for 'moved' clauses in 'copy_clause'
    // in the moving garbage collector 'copy_non_garbage_clauses'.
    // Otherwise 'literals' is valid.
  };

  long & analyzed () { assert (have_analyzed); return _analyzed; }

  const long & analyzed () const {
    assert (have_analyzed);
    return _analyzed;
  }

        int & pos ()       { assert (have_pos); return _pos; }
  const int & pos () const { assert (have_pos); return _pos; }

  literal_iterator       begin ()       { return literals; }
  literal_iterator         end ()       { return literals + size; }

  const_literal_iterator begin () const { return literals; }
  const_literal_iterator   end () const { return literals + size; }

  // Actual start of allocated memory, bytes allocated and offset are only
  // used for memory (de)allocation in 'delete_clause' and in the moving
  // garbage collector 'copy_non_garbage_clauses' and 'copy_clause'.
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
    return a->analyzed () < b->analyzed ();
  }
};

struct smaller_size {
  bool operator () (const Clause * a, const Clause * b) {
    return a->size < b->size;
  }
};

/*------------------------------------------------------------------------*/

inline size_t Clause::offset () const {
  size_t res = 0;
  if (!have_pos) res += sizeof _pos + sizeof dummy;
  if (!have_analyzed) res += sizeof _analyzed;
  assert (aligned (res, 8));
  return res;
}

inline size_t Clause::bytes () const {
  size_t res = sizeof (Clause);
  res += (size - 2) * sizeof (int);
  res -= offset ();
  res = align (res, 8);
  return res;
}

inline char * Clause::start () const {
  return offset () + (char*) this;
}

/*------------------------------------------------------------------------*/

// Place literals over the same variable close to each other.  This allows
// eager removal of identical literals and detection of tautological clauses
// and also is easier to read for debugging.

struct lit_less_than {
  bool operator () (int a, int b) const {
    int s = abs (a), t = abs (b);
    return s < t || (s == t && a < b);
  }
};

};

#endif
