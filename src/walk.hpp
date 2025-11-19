#ifndef _walk_hpp_INCLUDED
#define _walk_hpp_INCLUDED

#include "clause.hpp"

namespace CaDiCaL {
struct TaggedBinary {
  int lit, other;
#if defined(LOGGING) || !defined(NDEBUG)
  Clause *d;
#endif
  TaggedBinary ()
      : lit (0), other (0)
#if defined(LOGGING) || !defined(NDEBUG)
        ,
        d (nullptr)
#endif
  {
    assert (false);
  };

  TaggedBinary (Clause *c, int clit, int cother)
      : lit (clit), other (cother)
#if defined(LOGGING) || !defined(NDEBUG)
        ,
        d (c)
#endif
  {
#ifdef LOGGING
    assert (c->literals[0] == lit || c->literals[1] == lit);
    assert (c->literals[0] == other || c->literals[1] == other);
#endif

#ifndef LOGGING
    (void) c;
#endif
  }

  TaggedBinary (Clause *c) {
    assert (c->size == 2);
    lit = c->literals[0];
    other = c->literals[1];
#if defined(LOGGING) || !defined(NDEBUG)
    d = c;
#else
    (void) c;
#endif
  }
};

union clause_or_binary_raw {
  Clause *clause;
  TaggedBinary b;
  clause_or_binary_raw () : clause (nullptr) {}
};

// We experimented with using
//
//  using ClauseOrBinary = std::variant <Clause*, TaggedBinary>;
//
// instead of hand-rolling our own below, but the performance cost on
// vlsat2_144_7585.cnf.xz with a conflict limit of 2M conflicts was a
// factor 4 with:
//
// c        12.76    6.96% walkflipbroken
//
// vs
//
// c        49.86    22.63 % walkflipbroken
//
// And this is without doing any but stuffing to make the structure
// fit into 64 bits.
struct ClauseOrBinary {
  bool binary;
  clause_or_binary_raw tagged;
  ClauseOrBinary () : binary (false) { tagged.clause = nullptr; }
  ClauseOrBinary (Clause *c) : binary (false) { tagged.clause = c; }
  ClauseOrBinary (TaggedBinary &&c) : binary (true) { tagged.b = c; }
  bool is_binary () const { return binary; }
  Clause *clause () const {
    assert (!binary);
    return tagged.clause;
  }
  TaggedBinary &tagged_binary () {
    assert (binary);
    return tagged.b;
  }
};
} // namespace CaDiCaL

#endif
