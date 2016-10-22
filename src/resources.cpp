#include "internal.hpp"

#include <sys/time.h>
#include <sys/resource.h>

namespace CaDiCaL {

double Internal::seconds () {
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;  // user time
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec; // + system time
  return res;
}

void Internal::inc_bytes (size_t bytes) {
  if ((stats.bytes.total.current += bytes) > stats.bytes.total.max)
    stats.bytes.total.max = stats.bytes.total.current;
}

void Internal::dec_bytes (size_t bytes) {
  assert (stats.bytes.total.current >= bytes);
  stats.bytes.total.current -= bytes;
}

#define VECTOR_BYTES(V) \
  res += V.capacity () * sizeof (V[0])

size_t Internal::vector_bytes () {
  size_t res = 0;
  VECTOR_BYTES (original);
  VECTOR_BYTES (clause);
  VECTOR_BYTES (trail);
  VECTOR_BYTES (bump);
  VECTOR_BYTES (levels);
  VECTOR_BYTES (minimized);
  VECTOR_BYTES (resolved);
  VECTOR_BYTES (clauses);
  VECTOR_BYTES (levels);
  return res;
}

size_t Internal::max_bytes () {
  size_t res = stats.bytes.total.max;
  res += vector_bytes ();
  res += stats.bytes.watcher.max;
  return res;
}

size_t Internal::current_bytes () {
  size_t res = stats.bytes.total.current;
  res += vector_bytes ();
  res += stats.bytes.watcher.current;
  return res;
}

};
