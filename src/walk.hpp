#ifndef _walk_hpp_INCLUDED
#define _walk_hpp_INCLUDED

#include "clause.hpp"
#include <cstdint>



namespace CaDiCaL {

// Forward declarations
class Internal;

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
//
// We later switch to an even more compressed version with the binary flag and
// the rest being 63 bits.
struct ClauseOrBinary {
  // Use a bool for the binary flag and a union for the data.
  // The union must occupy 7 bytes (56 bits) to fit into 8 bytes total.
  // However, we enforce 63-bit fields to ensure no padding is added.

  // Union to store either a clause pointer (63 bits) or a TaggedBinary (63 bits).
  union clause_or_binary {
    // This is not portable C++, but it is unlikely that a compiler does
    // something different for the memory layout. We need (for to have
    // everything in 64 bits) to have `binary` in both branches and we rely on
    // the fact that there are at the same position.
    struct ClausePtr {
      bool binary : 1;
      uintptr_t clause_ptr : 63;  // 63 bits for clause pointer
      ClausePtr (): binary (0), clause_ptr(0) {};
    } clause;
    struct TaggedBinary {
      bool binary : 1;
      unsigned first_literal : 31;    // 31 bits for first literal
      int other : 32;

    #if defined(LOGGING) || !defined(NDEBUG)
      CaDiCaL::Clause *d;
    #endif
      TaggedBinary ()
          : first_literal (0), other (0)
    #if defined(LOGGING) || !defined(NDEBUG)
            ,
            d (nullptr)
    #endif
      {
        assert (false);
      };
      TaggedBinary (Internal *internal, CaDiCaL::Clause *c, unsigned clit, int cother);

      int lit (Internal *) const;
    } b;  // Must also occupy 63 bits
    clause_or_binary () : clause() {};
  } tagged;

  ClauseOrBinary () : tagged () {}

  // Constructor for non-binary clauses
  ClauseOrBinary (Internal *internal, Clause *c);
  ClauseOrBinary (Clause *c);

  // Constructor for binary clauses (from TaggedBinary)
  ClauseOrBinary (clause_or_binary::TaggedBinary &&binary) noexcept {
    tagged.b = binary;
  }

  // Constructor for binary clauses (from Clause*, lit, other)
  ClauseOrBinary (Internal *internal, Clause *d, int lit, int other) noexcept;

  bool is_binary () const { return tagged.b.binary; }

  Clause *clause () const {
    assert (!is_binary());
    return reinterpret_cast<Clause *>(tagged.clause.clause_ptr);
  }

  clause_or_binary::TaggedBinary &tagged_binary () {
    assert (is_binary());
    return tagged.b;
  }

  const clause_or_binary::TaggedBinary &tagged_binary () const {
    assert (is_binary());
    return tagged.b;
  }
};

// Ensure ClauseOrBinary occupies exactly 8 bytes in release builds
#if !defined(LOGGING) && defined(NDEBUG)
static_assert (sizeof (ClauseOrBinary) == 8, "ClauseOrBinary must occupy exactly 8 bytes in release builds");
#endif
} // namespace CaDiCaL

#endif
