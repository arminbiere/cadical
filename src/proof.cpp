#include "internal.hpp"

namespace CaDiCaL {

using namespace std;

/*------------------------------------------------------------------------*/

// Enable proof logging and checking by allocating a 'Proof' object.

void Internal::new_proof_on_demand () {
  if (!proof) {
    proof = new Proof (this);
    LOG ("connecting proof to internal solver");
  }
}

// Enable proof tracing.

void Internal::trace (File * file) {
  assert (!tracer);
  new_proof_on_demand ();
  tracer = new Tracer (this, file, opts.binary);
  LOG ("PROOF connecting proof tracer");
  proof->connect (tracer);
}

// Enable proof checking.

void Internal::check () {
  assert (!checker);
  new_proof_on_demand ();
  checker = new Checker (this);
  LOG ("PROOF connecting proof checker");
  proof->connect (checker);
}

// We want to close a proof trace and stop checking as soon we are done.

void Internal::close_trace () {
  assert (tracer);
  tracer->close ();
}

/*------------------------------------------------------------------------*/

Proof::Proof (Internal * s) : internal (s) { LOG ("PROOF new"); }

Proof::~Proof () { LOG ("PROOF delete"); }

/*------------------------------------------------------------------------*/

inline void Proof::add_literal (int internal_lit) {
  const int external_lit = internal->externalize (internal_lit);
  clause.push_back (external_lit);
}

inline void Proof::add_literals (Clause * c) {
  for (auto const & lit : * c)
    add_literal (lit);
}

inline void Proof::add_literals (const vector<int> & c) {
  for (auto const & lit : c)
    add_literal (lit);
}

/*------------------------------------------------------------------------*/

void Proof::add_original_clause (const vector<int> & c) {
  LOG (c, "PROOF adding original internal clause");
  add_literals (c);
  add_original_clause ();
}

void Proof::add_derived_empty_clause () {
  LOG ("PROOF adding empty clause");
  assert (clause.empty ());
  add_derived_clause ();
}

void Proof::add_derived_unit_clause (int internal_unit) {
  LOG ("PROOF adding unit clause %d", internal_unit);
  assert (clause.empty ());
  add_literal (internal_unit);
  add_derived_clause ();
}

/*------------------------------------------------------------------------*/

void Proof::add_derived_clause (Clause * c) {
  LOG (c, "PROOF adding to proof derived");
  assert (clause.empty ());
  add_literals (c);
  add_derived_clause ();
}

void Proof::delete_clause (Clause * c) {
  LOG (c, "PROOF deleting from proof");
  assert (clause.empty ());
  add_literals (c);
  delete_clause ();
}

void Proof::delete_clause (const vector<int> & c) {
  LOG (c, "PROOF deleting from proof");
  assert (clause.empty ());
  add_literals (c);
  delete_clause ();
}

void Proof::add_derived_clause (const vector<int> & c) {
  LOG (internal->clause, "PROOF adding derived clause");
  assert (clause.empty ());
  for (const auto & lit : c)
    add_literal (lit);
  add_derived_clause ();
}

/*------------------------------------------------------------------------*/

// During garbage collection clauses are shrunken by removing falsified
// literals. To avoid copying the clause, we provide a specialized tracing
// function here, which traces the required 'add' and 'remove' operations.

void Proof::flush_clause (Clause * c) {
  LOG (c, "PROOF flushing falsified literals in");
  assert (clause.empty ());
  for (int i = 0; i < c->size; i++) {
    int internal_lit = c->literals[i];
    if (internal->fixed (internal_lit) < 0) continue;
    add_literal (internal_lit);
  }
  add_derived_clause ();
  delete_clause (c);
}

// While strengthening clauses, e.g., through self-subsuming resolutions,
// during subsumption checking, we have a similar situation, except that we
// have to remove exactly one literal.  Again the following function allows
// to avoid copying the clause and instead provides tracing of the required
// 'add' and 'remove' operations.

void Proof::strengthen_clause (Clause * c, int remove) {
  LOG (c, "PROOF strengthen by removing %d in", remove);
  assert (clause.empty ());
  for (int i = 0; i < c->size; i++) {
    int internal_lit = c->literals[i];
    if (internal_lit == remove) continue;
    add_literal (internal_lit);
  }
  add_derived_clause ();
  delete_clause (c);
}

/*------------------------------------------------------------------------*/

void Proof::add_original_clause () {
  LOG (clause, "PROOF adding original external clause");
  for (size_t i = 0; i < observers.size (); i++)
    observers[i]->add_original_clause (clause);
  clause.clear ();
}

void Proof::add_derived_clause () {
  LOG (clause, "PROOF adding derived external clause");
  for (size_t i = 0; i < observers.size (); i++)
    observers[i]->add_derived_clause (clause);
  clause.clear ();
}

void Proof::delete_clause () {
  LOG (clause, "PROOF deleting external clause");
  for (size_t i = 0; i < observers.size (); i++)
    observers[i]->delete_clause (clause);
  clause.clear ();
}

}
