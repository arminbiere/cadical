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
  if ((stats.allocated += bytes) > stats.maxbytes)
    stats.maxbytes = stats.allocated;
}

void Internal::dec_bytes (size_t bytes) {
  assert (stats.allocated >= bytes);
  stats.allocated -= bytes;
}

size_t Internal::vector_bytes () {
  size_t res = 0;
  res += bytes_vector (trail);
  res += bytes_vector (clause);
  res += bytes_vector (levels);
  res += bytes_vector (analyzed);
  res += bytes_vector (minimized);
  res += bytes_vector (original);
  res += bytes_vector (extension);
  res += bytes_vector (control);
  res += bytes_vector (clauses);
  res += bytes_vector (resolved);
  res += bytes_vector (timers);
  return res;
}

size_t Internal::max_bytes () {
  size_t res = stats.maxbytes;
  res += vector_bytes ();
  return res;
}

size_t Internal::current_bytes () {
  size_t res = stats.allocated;
  res += vector_bytes ();
  return res;
}

};
