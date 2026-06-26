#include "internal.hpp"

namespace CaDiCaL {

Arena::Arena (Internal *i) : internal (i) {
  // avoids a clang++ warning when compiling without LOGGING
  (void) internal;
  from.start = from.top = from.end = to.start = to.end = to.top = nullptr;
}

Arena::~Arena () {
  delete[] from.start;
  delete[] to.start;
}

void Arena::prepare (size_t bytes) {
  LOG ("preparing 'to' space of arena with %zd bytes", bytes);
  assert (!to.start);
  to.top = to.start = new char[bytes];
  to.end = to.start + bytes;
}

void Arena::swap () {
  delete[] from.start;
  LOG ("delete 'from' space of arena with %zd bytes",
       (size_t) (from.end - from.start));
  from = to;
  to.start = to.top = to.end = 0;
}

bool Arena::contains (Clause *p) const {
  const bool with_lrat = internal->requires_id;
  char *c = (char *) p;
  if (!with_lrat)
    c += Clause::offset (p->allocated_as_binary ());
  return (from.start <= c && c < from.top) ||
         (to.start <= c && c < to.top);
}
} // namespace CaDiCaL
