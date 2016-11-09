#include "internal.hpp"
#include "iterator.hpp"
#include "macros.hpp"

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

void Internal::connect_watches () {
  START (connect);
  assert (watches ());
  LOG ("connecting all watches");
  const const_clause_iterator end = clauses.end ();
  for (const_clause_iterator i = clauses.begin (); i != end; i++)
    watch_clause (*i);
  STOP (connect);
}

};
