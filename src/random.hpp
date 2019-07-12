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
