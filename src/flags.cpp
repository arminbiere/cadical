#include "internal.hpp"
#include "iterator.hpp"
#include "clause.hpp"

namespace CaDiCaL {

void Internal::mark (Clause * c) {
  const const_literal_iterator end = c->end ();
  const_literal_iterator k;
  for (k = c->begin (); k != end; k++) mark (*k);
}

void Internal::unmark (Clause * c) {
  const const_literal_iterator end = c->end ();
  const_literal_iterator k;
  for (k = c->begin (); k != end; k++) unmark (*k);
}

void Internal::mark_clause () {
  const const_int_iterator end = clause.end ();
  const_int_iterator k;
  for (k = clause.begin (); k != end; k++) mark (*k);
}

void Internal::unmark_clause () {
  const const_int_iterator end = clause.end ();
  const_int_iterator k;
  for (k = clause.begin (); k != end; k++) unmark (*k);
}

};
