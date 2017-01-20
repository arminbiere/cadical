#include "internal.hpp"

namespace CaDiCaL {

Arena::Arena (Internal * i) {
  memset (this, 0, sizeof *this);
  internal = i;
}

Arena::~Arena () {
  delete [] from.start;
  delete [] to.start;
}

void Arena::prepare (size_t bytes) {
  assert (aligned (bytes, 8));
  LOG ("preparing 'to' space of arena with %ld bytes", (long) bytes);
  assert (!to.start);
  to.top = to.start = new char[bytes];
  to.end = to.start + bytes;
  assert (aligned (to.start, 8));
}

void Arena::swap () {
  delete [] from.start;
  LOG ("delete 'from' space of arena with %ld bytes",
    (long) (from.end - from.start));
  from = to;
  to.start = to.top = to.end = 0;
}

};
