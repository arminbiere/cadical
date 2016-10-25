#include "internal.hpp"

#include <cassert>

namespace CaDiCaL {

void Internal::unwatch_literal (int lit, Clause * c) {
  LOG (c, "unwatch %d in", lit);
  assert (c->literals[0] == lit || c->literals[1] == lit);
  Watches & ws = watches (lit);
  const const_watch_iterator end = ws.end ();
  watch_iterator j = ws.begin ();
  for (const_watch_iterator i = j; i != end; i++)
    if ((*j++ = *i).clause == c) j--;
  assert (j + 1 == end);
  ws.resize (j - ws.begin ());
}

};
