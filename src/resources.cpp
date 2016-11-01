#include "internal.hpp"
#include "macros.hpp"

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

size_t Internal::vector_bytes () {
  size_t res = 0;
  res += VECTOR_BYTES (trail);
  res += VECTOR_BYTES (clause);
  res += VECTOR_BYTES (levels);
  res += VECTOR_BYTES (analyzed);
  res += VECTOR_BYTES (minimized);
  res += VECTOR_BYTES (original);
  res += VECTOR_BYTES (extension);
  res += VECTOR_BYTES (control);
  res += VECTOR_BYTES (clauses);
  res += VECTOR_BYTES (resolved);
  res += VECTOR_BYTES (timers);
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
