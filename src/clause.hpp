#ifndef _clause_hpp_INCLUDED
#define _clause_hpp_INCLUDED

#include <cstdlib>

namespace CaDiCaL {

// The 'Clause' data structure is very important. There are usually many
// clauses and accessing them is a hot-spot.  Thus we use three common
// optimizations to reduce their memory foot print and improve cache usage.
//
// (1) The most important optimization is to 'embed' the actual literals in
// the clause.  This requires a variadic size structure and thus strictly is
// not 'C' conformant, but supported by all compilers we used.  The
// alternative is to store the actual literals somewhere else, which
// not only needs more memory but more importantly also requires another
// memory access and thus is so costly that even for CaDiCaL we want to use
// this optimizations.
//
// (2) The boolean flags only need one bit each and thus there is enough
// space left to merge them with a 'glue' bit field (which is less accessed
// than 'size').  This saves 4 bytes and also keeps the header without
// 'resolved' nicely in 8 bytes.  We currently use 28 bits and actually
// since we do not want to mess with 'unsigned' versus 'signed' issues just
// use 27 out of them.  If more boolean flags are needed this number has to
// be adapted accordingly.
//
// (3) Original clauses and clauses with small glue or size are kept anyhow and o
// not need the activity counter 'resolved'.  Thus we can omit these 8 bytes for
// these clauses.  Redundant clauses of long size and with large glue have a
// 'resolved' field and are called 'extended'.  The non extended clauses need 8
// bytes less and accessing 'resolved' for them is not allowed.
//
// With these three optimizations a binary original clause only needs 16
// bytes instead of 40 bytes without embedding and 32 bytes with embedding
// the literals.  The last two optimizations reduce memory usage of very
// large formulas slightly but are otherwise not that important.
//
// If you want to add few additional boolean flags add them after the
// sequence of already existing ones.  This makes sure that these bits and
// the following 'glue' field are put into a 4 byte word by the compiler. Of course
// you need to adapt 'LD_MAX_GLUE' accordingly.  Adding one flag reduces it by one.
//
// Similarly if you want to add more data to extended clauses put these
// fields after 'resolved' and before the flags section.  Then adapt the
// 'EXTENDED_OFFSET' accordingly.  You might need to consider padding though
// on some architectures, since misaligned pointer access might happen.
// For instance if you want to add a 4 byte 'int data' field, then you
// should also add a 'int padding' field, just to enforce that the
// 'resolved' field is always 8 byte aligned.  Here we assume that 'new'
// returns 8 bytes aligned memory, which on those systems which care about
// alignment is true for sure.
//
// Additional fields needed for all clauses are savely put between 'glue'
// and 'size' without the need to change anything else.  In general these
// optimizations are local to 'clause.[hc]pp' and otherwise can be ignored
// except that you should for instance never access 'resolved' of a clauses
// which is not extended.  This can be checked with for instance 'valgrind' 
// but is also guarded by making the actual '_resolved' field private and
// checking this contract in the 'resolved ()' accessor functions.

#define LD_MAX_GLUE     28      // 32 - 4 boolean flags
#define EXTENDED_OFFSET  8      // sizeof (resolved)

#define MAX_GLUE ((1<<(LD_MAX_GLUE-1))-1)

class Clause {

  long _resolved;        // time stamp when resolved last time

public:

  unsigned extended:1;  // 'resolved' field only valid this is true
  unsigned redundant:1; // aka 'learned' so not 'irredundant' (original)
  unsigned garbage:1;   // can be garbage collected unless it is a 'reason'
  unsigned reason:1;    // reason / antecedent clause can not be collected

  // This is the 'glue' = 'glucose level' = 'LBD' of a redundant clause.
  // We actually only use 'CLAUSE_LD_MAX_GLUE-1' bits since the field is
  // 'signed' to avoid surprises due to 'unsigned' versus 'sign' semantics.
  // Also note that 'C' does not explicitly define 'signedness' of 'int' bit
  // fields and thus we explicitly have to use 'signed' here (on an IBM main
  // frame or on Sparc 'int a:1' might be 'unsigned').
  // 
  signed int glue : LD_MAX_GLUE;

  int size;             // actual size of 'literals' (at least 2)
  int literals[2];      // of variadic 'size' (not 2) in general

  static size_t bytes (int size) {
    return sizeof (Clause) + (size -2 ) * sizeof (int);
  }

  long & resolved () { assert (extended); return _resolved; }
  const long & resolved () const { assert (extended); return _resolved; }
};

struct resolved_earlier {
  bool operator () (const Clause * a, const Clause * b) {
    assert (a->extended), assert (b->extended); 
    return a->resolved () < b->resolved ();
  }
};

};

#endif
