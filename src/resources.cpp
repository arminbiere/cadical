#include "cadical.hpp"

namespace CaDiCaL {

void Solver::inc_bytes (size_t bytes) {
  if ((stats.bytes.total.current += bytes) > stats.bytes.total.max)
    stats.bytes.total.max = stats.bytes.total.current;
}

void Solver::dec_bytes (size_t bytes) {
  assert (stats.bytes.total.current >= bytes);
  stats.bytes.total.current -= bytes;
}

#define VECTOR_BYTES(V) \
  res += V.capacity () * sizeof (V[0])

size_t Solver::vector_bytes () {
  size_t res = 0;
#ifndef NDEBUG
  VECTOR_BYTES (original_literals);
#endif
  VECTOR_BYTES (clause);
  VECTOR_BYTES (trail);
  VECTOR_BYTES (seen.literals);
  VECTOR_BYTES (seen.levels);
  VECTOR_BYTES (seen.minimized);
  VECTOR_BYTES (resolved);
  VECTOR_BYTES (clauses);
  VECTOR_BYTES (levels);
  return res;
}

size_t Solver::max_bytes () {
  size_t res = stats.bytes.total.max + vector_bytes ();
  if (stats.bytes.watcher.max > 0) res += stats.bytes.watcher.max;
  else res += (4 * stats.clauses.max * sizeof (Watch)) / 3;
  return res;
}

size_t Solver::current_bytes () {
  size_t res = stats.bytes.total.current + vector_bytes ();
  if (stats.bytes.watcher.current > 0) res += stats.bytes.watcher.current;
  else res += (4 * stats.clauses.current * sizeof (Watch)) / 3;
  return res;
}

};
