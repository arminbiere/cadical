#include "internal.hpp"

namespace CaDiCaL {

using namespace std;

/*------------------------------------------------------------------------*/

// Enable proof logging and checking by allocating a 'Proof' object.

void Internal::new_proof_on_demand () {
  if (!proof) {
    proof = new Proof (this);
    LOG ("connecting proof to internal solver");
    build_full_lrat ();
  }
}

void Internal::build_full_lrat () {
  assert (!lratbuilder);
  if (!opts.lratexternal)
    return;
  lratbuilder = new LratBuilder (this);
  LOG ("PROOF connecting lrat proof chain builder");
  proof->connect (lratbuilder);
}

// Enable proof tracing.

void Internal::trace (File *file) {
  assert (!tracer);
  new_proof_on_demand ();
  tracer = new Tracer (this, file, opts.binary, opts.lrat, opts.lratfrat);
  LOG ("PROOF connecting proof tracer");
  proof->connect (tracer);
}

// Enable proof checking.

void Internal::check () {
  assert (!checker);
  assert (!lratchecker);
  new_proof_on_demand ();
  if (opts.checkprooflrat) {
    lratchecker = new LratChecker (this);
    LOG ("PROOF connecting lrat proof checker");
    proof->connect (lratchecker);
  } else {
    checker = new Checker (this);
    LOG ("PROOF connecting proof checker");
    proof->connect (checker);
  }
}

// We want to close a proof trace and stop checking as soon we are done.

void Internal::close_trace () {
  assert (tracer);
  tracer->close ();
}

// We can flush a proof trace file before actually closing it.

void Internal::flush_trace () {
  assert (tracer);
  tracer->flush ();
}

/*------------------------------------------------------------------------*/

Proof::Proof (Internal *s)
    : internal (s), checker (0), tracer (0), lratbuilder (0),
      lratchecker (0) {
  LOG ("PROOF new");
}

Proof::~Proof () { LOG ("PROOF delete"); }

/*------------------------------------------------------------------------*/

inline void Proof::add_literal (int internal_lit) {
  const int external_lit = internal->externalize (internal_lit);
  clause.push_back (external_lit);
}

inline void Proof::add_literals (Clause *c) {
  for (auto const &lit : *c)
    add_literal (lit);
}

inline void Proof::add_literals (const vector<int> &c) {
  for (auto const &lit : c)
    add_literal (lit);
}

/*------------------------------------------------------------------------*/

void Proof::add_original_clause (uint64_t id, const vector<int> &c) {
  LOG (c, "PROOF adding original internal clause");
  add_literals (c);
  clause_id = id;
  add_original_clause ();
}

void Proof::add_external_original_clause (uint64_t id,
                                          const vector<int> &c) {
  // literals of c are already external
  assert (clause.empty ());
  for (auto const &lit : c)
    clause.push_back (lit);
  clause_id = id;
  add_original_clause ();
}

void Proof::delete_external_original_clause (uint64_t id,
                                             const vector<int> &c) {
  // literals of c are already external
  assert (clause.empty ());
  for (auto const &lit : c)
    clause.push_back (lit);
  clause_id = id;
  delete_clause ();
}

void Proof::add_derived_empty_clause (uint64_t id) {
  LOG ("PROOF adding empty clause");
  assert (clause.empty ());
  clause_id = id;
  add_derived_clause ();
}

void Proof::add_derived_unit_clause (uint64_t id, int internal_unit) {
  LOG ("PROOF adding unit clause %d", internal_unit);
  assert (clause.empty ());
  add_literal (internal_unit);
  clause_id = id;
  add_derived_clause ();
}

void Proof::add_derived_empty_clause (uint64_t id,
                                      const vector<uint64_t> &chain) {
  LOG ("PROOF adding empty clause");
  assert (clause.empty ());
  assert (proof_chain.empty ());
  for (const auto &cid : chain)
    proof_chain.push_back (cid);
  clause_id = id;
  add_derived_clause ();
}

void Proof::add_derived_unit_clause (uint64_t id, int internal_unit,
                                     const vector<uint64_t> &chain) {
  LOG ("PROOF adding unit clause %d", internal_unit);
  assert (proof_chain.empty ());
  assert (clause.empty ());
  add_literal (internal_unit);
  for (const auto &cid : chain)
    proof_chain.push_back (cid);
  clause_id = id;
  add_derived_clause ();
}

/*------------------------------------------------------------------------*/

void Proof::add_derived_clause (Clause *c) {
  LOG (c, "PROOF adding to proof derived");
  assert (clause.empty ());
  add_literals (c);
  clause_id = c->id;
  add_derived_clause ();
}

void Proof::add_derived_clause (uint64_t id, const vector<int> &c) {
  LOG (internal->clause, "PROOF adding derived clause");
  assert (clause.empty ());
  for (const auto &lit : c)
    add_literal (lit);
  clause_id = id;
  add_derived_clause ();
}

void Proof::add_derived_clause (Clause *c, const vector<uint64_t> &chain) {
  LOG (c, "PROOF adding to proof derived");
  assert (clause.empty ());
  assert (proof_chain.empty ());
  add_literals (c);
  for (const auto &cid : chain)
    proof_chain.push_back (cid);
  clause_id = c->id;
  add_derived_clause ();
}

void Proof::add_derived_clause (uint64_t id, const vector<int> &c,
                                const vector<uint64_t> &chain) {
  LOG (internal->clause, "PROOF adding derived clause");
  assert (clause.empty ());
  assert (proof_chain.empty ());
  for (const auto &lit : c)
    add_literal (lit);
  for (const auto &cid : chain)
    proof_chain.push_back (cid);
  clause_id = id;
  add_derived_clause ();
}

void Proof::delete_clause (Clause *c) {
  LOG (c, "PROOF deleting from proof");
  assert (clause.empty ());
  add_literals (c);
  clause_id = c->id;
  delete_clause ();
}

void Proof::delete_clause (uint64_t id, const vector<int> &c) {
  LOG (c, "PROOF deleting from proof");
  assert (clause.empty ());
  add_literals (c);
  clause_id = id;
  delete_clause ();
}

void Proof::delete_unit_clause (uint64_t id, const int lit) {
  LOG ("PROOF deleting unit from proof %d", lit);
  assert (clause.empty ());
  add_literal (lit);
  clause_id = id;
  delete_clause ();
}

void Proof::finalize_clause (Clause *c) {
  LOG (c, "PROOF finalizing clause");
  assert (clause.empty ());
  add_literals (c);
  clause_id = c->id;
  finalize_clause ();
}

void Proof::finalize_clause (uint64_t id, const vector<int> &c) {
  LOG (c, "PROOF finalizing clause");
  assert (clause.empty ());
  for (const auto &lit : c)
    add_literal (lit);
  clause_id = id;
  finalize_clause ();
}

void Proof::finalize_unit (uint64_t id, int lit) {
  LOG ("PROOF finalizing clause %d", lit);
  assert (clause.empty ());
  add_literal (lit);
  clause_id = id;
  finalize_clause ();
}

/*------------------------------------------------------------------------*/

// During garbage collection clauses are shrunken by removing falsified
// literals. To avoid copying the clause, we provide a specialized tracing
// function here, which traces the required 'add' and 'remove' operations.

void Proof::flush_clause (Clause *c) {
  LOG (c, "PROOF flushing falsified literals in");
  assert (clause.empty ());
  for (int i = 0; i < c->size; i++) {
    int internal_lit = c->literals[i];
    if (internal->fixed (internal_lit) < 0) {
      const unsigned uidx = internal->vlit (-internal_lit);
      uint64_t id = internal->unit_clauses[uidx];
      assert (id);
      proof_chain.push_back (id);
      continue;
    }
    add_literal (internal_lit);
  }
  proof_chain.push_back (c->id);
  int64_t id = ++internal->clause_id;
  clause_id = id;
  add_derived_clause ();
  delete_clause (c);
  c->id = id;
}

// While strengthening clauses, e.g., through self-subsuming resolutions,
// during subsumption checking, we have a similar situation, except that we
// have to remove exactly one literal.  Again the following function allows
// to avoid copying the clause and instead provides tracing of the required
// 'add' and 'remove' operations.

void Proof::strengthen_clause (Clause *c, int remove) {
  LOG (c, "PROOF strengthen by removing %d in", remove);
  assert (clause.empty ());
  for (int i = 0; i < c->size; i++) {
    int internal_lit = c->literals[i];
    if (internal_lit == remove)
      continue;
    add_literal (internal_lit);
  }
  int64_t id = ++internal->clause_id;
  clause_id = id;
  add_derived_clause ();
  delete_clause (c);
  c->id = id;
}

void Proof::strengthen_clause (Clause *c, int remove,
                               const vector<uint64_t> &chain) {
  LOG (c, "PROOF strengthen by removing %d in", remove);
  assert (clause.empty ());
  for (int i = 0; i < c->size; i++) {
    int internal_lit = c->literals[i];
    if (internal_lit == remove)
      continue;
    add_literal (internal_lit);
  }
  int64_t id = ++internal->clause_id;
  clause_id = id;
  for (const auto &cid : chain)
    proof_chain.push_back (cid);
  add_derived_clause ();
  delete_clause (c);
  c->id = id;
}

void Proof::otfs_strengthen_clause (Clause *c,
                                    const std::vector<int> &old) {
  LOG (c, "PROOF otfs strengthen");
  assert (clause.empty ());
  for (int i = 0; i < c->size; i++) {
    int internal_lit = c->literals[i];
    add_literal (internal_lit);
  }
  int64_t id = ++internal->clause_id;
  clause_id = id;
  add_derived_clause ();
  delete_clause (c->id, old);
  c->id = id;
}

void Proof::otfs_strengthen_clause (Clause *c, const std::vector<int> &old,
                                    const vector<uint64_t> &chain) {
  LOG (c, "PROOF otfs strengthen");
  assert (clause.empty ());
  for (int i = 0; i < c->size; i++) {
    int internal_lit = c->literals[i];
    add_literal (internal_lit);
  }
  int64_t id = ++internal->clause_id;
  clause_id = id;
  for (const auto &cid : chain)
    proof_chain.push_back (cid);
  add_derived_clause ();
  delete_clause (c->id, old);
  c->id = id;
}

/*------------------------------------------------------------------------*/

void Proof::add_original_clause () {
  LOG (clause, "PROOF adding original external clause");
  assert (clause_id);

  if (lratbuilder)
    lratbuilder->add_original_clause (clause_id, clause);
  if (lratchecker)
    lratchecker->add_original_clause (clause_id, clause);
  if (checker)
    checker->add_original_clause (clause_id, clause);
  if (tracer)
    tracer->add_original_clause (clause_id, clause);
  clause.clear ();
  clause_id = 0;
}

void Proof::add_derived_clause () {
  LOG (clause, "PROOF adding derived external clause");
  assert (clause_id);
  assert (!internal->opts.lrat || internal->opts.lratexternal ||
          !proof_chain.empty ());

  if (lratbuilder) {
    if (proof_chain.empty ())
      proof_chain = lratbuilder->add_clause_get_proof (clause_id, clause);
    else
      lratbuilder->add_derived_clause (clause_id, clause);
  }
  if (lratchecker) {
    if (proof_chain.empty ())
      lratchecker->add_derived_clause (clause_id, clause);
    else
      lratchecker->add_derived_clause (clause_id, clause, proof_chain);
  }
  if (checker)
    checker->add_derived_clause (clause_id, clause);
  if (tracer) {
    if (proof_chain.empty ())
      tracer->add_derived_clause (clause_id, clause);
    else
      tracer->add_derived_clause (clause_id, clause, proof_chain);
  }
  proof_chain.clear ();
  clause.clear ();
  clause_id = 0;
}

void Proof::delete_clause () {
  LOG (clause, "PROOF deleting external clause");
  if (lratbuilder)
    lratbuilder->delete_clause (clause_id, clause);
  if (lratchecker)
    lratchecker->delete_clause (clause_id, clause);
  if (checker)
    checker->delete_clause (clause_id, clause);
  if (tracer)
    tracer->delete_clause (clause_id, clause);
  clause.clear ();
  clause_id = 0;
}

void Proof::finalize_clause () {
  if (tracer)
    tracer->finalize_clause (clause_id, clause);
  clause.clear ();
  clause_id = 0;
}

} // namespace CaDiCaL
