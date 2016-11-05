#include "internal.hpp"
#include "iterator.hpp"

namespace CaDiCaL {

void Internal::init_watches () {
  assert (!wtab);
  wtab = new Watches [2*vsize];
}

size_t Internal::bytes_watches () {
  assert (watches ());
  size_t bytes = 0;
  for (int idx = 1; idx <= max_var; idx++)
    bytes += bytes_vector (watches (idx)),
    bytes += bytes_vector (watches (-idx));
  return bytes;
}

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

void Internal::connect_watches () {
  assert (watches ());
  LOG ("connecting all watches");
  const const_clause_iterator end = clauses.end ();
  for (const_clause_iterator i = clauses.begin (); i != end; i++)
    watch_clause (*i);
}

};
