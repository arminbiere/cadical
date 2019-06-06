/*------------------------------------------------------------------------*/

// Since 'cstdint' and 'stdint.h' only became available with C11 we
// provide a work-around which tries to figure out proper 64 bit values
// during configuration and otherwise uses the types below.

#if !defined (NSTDINT) && !defined(uint64_t) && !defined(uint32_t)
#include <cstdint>
#else
#ifndef uint64_t
typedef size_t uint64_t;
#endif
#ifndef uint32_t
typedef unsigned uint32_t;
#endif
#endif // end of '#if !define(NSTDINT) ...'

/*------------------------------------------------------------------------*/

// Random number generator.

namespace CaDiCaL {

class Random {

  uint64_t state;

  void add (uint64_t a) {
    if (!(state += a)) state = 1;
    next ();
  }

public:

  // Without argument use a machine, process and time dependent seed.
  //
  Random ();

  Random (uint64_t seed) : state (seed) { }
  Random (const Random & other) : state (other.seed ()) { }

  void operator += (uint64_t a) { add (a); }
  uint64_t seed () const { return state; }

  uint64_t next () {
    state *= 6364136223846793005ul;
    state += 1442695040888963407ul;
    assert (state);
    return state;
  }

  uint32_t generate () { next (); return state >> 32; }
  int      generate_int () { return (int) generate (); }
  bool     generate_bool () { return generate () < 2147483648u; }

  // Generate 'double' value in the range '[0,1]'.
  //
  double generate_double () { return generate () / 4294967295.0; }

  // Generate 'int' value in the range '[l,r]'.
  //
  int pick_int (int l, int r) {
    assert (l <= r);
    int res = (r + 1.0 - l) * (generate () / 4294967296.0);
    res += l;
    assert (l <= res);
    assert (res <= r);
    return res;
  }

  // Generate 'double' value in the range '[l,r]'.
  //
  double pick_double (double l, double r) {
    assert (l <= r);
    double res = (r - l) * generate_double ();
    res += l;
    assert (l <= res);
    assert (res <= r);
    return res;
  }
};

}
