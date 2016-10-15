#include "internal.hpp"

namespace CaDiCaL {

Arena::Arena (Internal * i) {
  memset (this, 0, sizeof *this);
  internal = i;
}

Arena::~Arena () {
  internal->dec_bytes (from.end - from.start);
  internal->dec_bytes (to.end - to.start);
  delete [] from.start;
  delete [] to.start;
}

void Arena::prepare (size_t bytes) {
  LOG ("preparing 'to' space of arena with %ld bytes", (long) bytes);
  assert (!to.start);
  internal->inc_bytes (bytes);
  to.top = to.start = new char[bytes];
  to.end = to.start + bytes;
}

void Arena::swap () {
  size_t bytes = from.end - from.start;
  internal->dec_bytes (bytes);
  delete [] from.start;
  LOG ("delete 'from' space of arena with %ld bytes", (long) bytes);
  from = to;
  to.start = to.top = to.end = 0;
}

};
