#include "proof.hpp"
#include "cadical.hpp"
#include "logging.hpp"

#include <cassert>

namespace CaDiCaL {

void Proof::trace_empty_clause () {
  assert (enabled);
  LOG ("tracing empty clause");
  print ("0\n", proof_file);
}

void Proof::trace_unit_clause (int unit) {
  if (!proof_file) return;
  LOG ("tracing unit clause %d", unit);
  print (unit, proof_file);
  print (" 0\n", proof_file);
}

void Proof::trace_clause (Clause * c, bool add) {
  if (!proof_file) return;
  LOG (c, "tracing %s", add ? "addition" : "deletion");
  if (!add) print ("d ", proof_file);
  const int size = c->size, * lits = c->literals;
  for (int i = 0; i < size; i++)
    print (lits[i], proof_file), print (" ", proof_file);
  print ("0\n", proof_file);
}

void Proof::trace_add_clause (Clause * c) { trace_clause (c, true); }

void Proof::trace_delete_clause (Clause * c) { trace_clause (c, false); }

void Proof::trace_flushing_clause (Solver * s, Clause * c) {
  if (!proof_file) return;
  LOG (c, "tracing flushing");
  const int size = c->size, * lits = c->literals;
  for (int i = 0; i < size; i++) {
    const int lit = lits[i];
    if (s->fixed (lit) >= 0)
      print (lit, proof_file), print (" ", proof_file);
  }
  print ("0\nd ", proof_file);
  for (int i = 0; i < size; i++)
    print (lits[i], proof_file), print (" ", proof_file);
  print ("0\n", proof_file);
}

};
