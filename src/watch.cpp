#include "internal.hpp"
#include "iterator.hpp"
#include "macros.hpp"

namespace CaDiCaL {

void Internal::init_watches () {
  assert (!wtab);
  wtab = new Watches [2*vsize];
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
  for (const_clause_iterator i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (!c->garbage) watch_clause (c);
  }
  STOP (connect);
}

};
