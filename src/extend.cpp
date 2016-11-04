#include "internal.hpp"
#include "message.hpp"
#include "macros.hpp"

namespace CaDiCaL {

void Internal::extend () {
  START (extend);
  long flipped = 0;
  VRB ("extend",
    "extending through extension stack of size %ld",
    extension.size ());
  const const_int_iterator begin = extension.begin ();
  const_int_iterator i = extension.end ();
  while (i != begin) {
    bool satisfied = false;
    int lit, last = 0;
    assert (i != begin);
    while ((lit = *--i)) {
      if (val (lit) > 0) satisfied = true;
      assert (i != begin);
      last = lit;
    }
    if (satisfied) continue;
    flipped++;
    assert (last);
    LOG ("flipping blocking literal %d", last);
    const int idx = vidx (last);
    const int tmp = sign (last);
    vals[idx] = phases[idx] = tmp;
    vals[-idx] = -tmp;
  }
  VRB ("extend", "flipped %ld literals during extension", flipped);
  STOP (extend);
}

};
