#include "internal.hpp"
#include "iterator.hpp"

namespace CaDiCaL {

void Internal::init_watches () {
  assert (!wtab);
  wtab = new Watches [2*vsize];
}

// TODO remove?
#if 0
size_t Internal::implicit_watches_bytes () {
  assert (wtab);
  size_t res = 0;
  for (int idx = 1; idx <= max_var; idx++)
    res += bytes_vector (watches (idx)),
    res += bytes_vector (watches (-idx));
  return res;
}
#endif

void Internal::reset_watches () {
  assert (wtab);
  delete [] wtab;
  wtab = 0;
}

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
