#include "internal.hpp"
#include "macros.hpp"

#include <sys/time.h>
#include <sys/resource.h>

namespace CaDiCaL {

double process_time () {
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;  // user time
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec; // + system time
  return res;
}

size_t maximum_resident_set_size () {
  struct rusage u;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  return u.ru_maxrss;
}

inline void Internal::update_max_bytes () {
  size_t really_allocated = stats.allocated + stats.implicit;
  if (really_allocated > stats.maxbytes) stats.maxbytes = really_allocated;
}

void Internal::inc_bytes (size_t bytes) {
  stats.allocated += bytes;
  update_max_bytes ();
}

void Internal::dec_bytes (size_t bytes) {
  assert (stats.allocated >= bytes);
  stats.allocated -= bytes;
}

// We do this once in a while to approximate the actual number of allocated
// bytes taking all the implicit memory used in vectors into account.  An
// alternative would be to add a wrapper around 'std::vector' which updates
// memory statistics eagerly.  This is however awkward to use since it
// requires an 'Internal' argument to every 'push_back' etc.  It might also
// be slightly slower.

// The risk of this approach is that we forget to include an important
// vector and further updating might not accurate enough in time.

void Internal::account_implicitly_allocated_bytes () {
  size_t bytes = 0;
  bytes += bytes_vector (trail);
  bytes += bytes_vector (clause);
  bytes += bytes_vector (levels);
  bytes += bytes_vector (analyzed);
  bytes += bytes_vector (minimized);
  bytes += bytes_vector (original);
  bytes += bytes_vector (extension);
  bytes += bytes_vector (control);
  bytes += bytes_vector (clauses);
  bytes += bytes_vector (resolved);
  bytes += bytes_vector (timers);
  if (occs ()) bytes += bytes_occs ();
  if (watches ()) bytes += bytes_watches ();
  LOG ("now %ld instead of %ld bytes implicitly allocated",
    (long) stats.implicit, (long) bytes);
  stats.implicit = bytes;
  update_max_bytes ();
  if (opts.verbose) report ('a');
}

size_t Internal::max_bytes () { return stats.maxbytes; }

size_t Internal::current_bytes () {
  if (!stats.implicit) account_implicitly_allocated_bytes ();
  return stats.allocated + stats.implicit;
}

};
