#include "proof.hpp"
#include "cadical.hpp"
#include "logging.hpp"
#include "clause.hpp"
#include "file.hpp"

#include <cassert>

namespace CaDiCaL {

using namespace std;

void Proof::trace_empty_clause (Solver * solver) {
  if (!enabled) return;
  LOG ("tracing empty clause");
  file->put ("0\n");
}

void Proof::trace_unit_clause (Solver * solver, int unit) {
  if (!enabled) return;
  LOG ("tracing unit clause %d", unit);
  file->put (unit);
  file->put (" 0\n");
}

void Proof::trace_clause (Solver * solver, Clause * c, bool add) {
  if (!enabled) return;
  LOG (c, "tracing %s", add ? "addition" : "deletion");
  if (!add) file->put ("d ");
  const int size = c->size, * lits = c->literals;
  for (int i = 0; i < size; i++)
    file->put (lits[i]), file->put (" ");
  file->put ("0\n");
}

void Proof::trace_add_clause (Solver * solver, Clause * c) {
  trace_clause (solver, c, true);
}

void Proof::trace_delete_clause (Solver * solver, Clause * c) {
  trace_clause (solver, c, false);
}

void Proof::trace_flushing_clause (Solver * solver, Clause * c) {
  if (!enabled) return;
  LOG (c, "tracing flushing");
  const int size = c->size, * lits = c->literals;
  for (int i = 0; i < size; i++) {
    const int lit = lits[i];
    if (solver->fixed (lit) >= 0)
      file->put (lit), file->put (" ");
  }
  file->put ("0\nd ");
  for (int i = 0; i < size; i++)
    file->put (lits[i]), file->put (" ");
  file->put ("0\n");
}

};
