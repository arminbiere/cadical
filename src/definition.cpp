#include "internal.hpp"

namespace CaDiCaL {

#define INVALID_LIT UINT_MAX

// functions below are passed to kitten
//
struct definition_extractor {
  Eliminator *eliminator;
  Internal *internal;
  vector<Clause*> clauses[2];
  int lit;
  vector<vector<int>> implicants;
  int unit;
};


extern "C" {

// used to extract definitions from kitten
//
static void traverse_definition_core (void *state, unsigned id) {
  definition_extractor *extractor = (definition_extractor *) state;
  Clause *clause;
  const vector<Clause*> &clauses0 = extractor->clauses[0];
  const vector<Clause*> &clauses1 = extractor->clauses[1];
  Eliminator *eliminator = extractor->eliminator;
  const size_t size_clauses0 = clauses0.size ();
  const size_t size_clauses1 = clauses1.size ();
  assert (size_clauses0 <= UINT_MAX);
  unsigned sign;
  if (id >= size_clauses0 + size_clauses1) {
    unsigned tmp = id - size_clauses0 - size_clauses1;
    assert (tmp < extractor->implicants.size ());
    eliminator->definition_unit |= 3;
    eliminator->prime_gates.push_back (extractor->implicants[tmp]);
    return;
  }
  if (id < size_clauses0) {
    clause = clauses0[id];
    sign = 1;
  } else {
    unsigned tmp = id - size_clauses0;
#ifndef NDEBUG
    assert (size_clauses1 <= UINT_MAX);
    assert (tmp < size_clauses1);
#endif
    clause = clauses1[tmp];
    sign = 2;
  }
  clause->gate = true;
  eliminator->gates.push_back (clause);
#ifdef LOGGING
  Internal *internal = extractor->internal;
  LOG (clause, "extracted gate");
#endif
  eliminator->definition_unit |= sign;
}

// extracts relevant learned clauses from kissat for drat proofs
//
static void traverse_one_sided_core_lemma (void *state, bool learned,
                                           size_t size,
                                           const unsigned *lits) {
  if (!learned)
    return;
  definition_extractor *extractor = (definition_extractor *) state;
  Eliminator *eliminator = extractor->eliminator;
  Internal *internal = extractor->internal;
  Proof *proof = internal->proof;
  const int unit = extractor->unit;
  vector<proof_clause> &proof_clauses = eliminator->proof_clauses;
  if (size) {
    proof_clause pc;
    pc.id = ++(internal->clause_id);
    pc.literals.push_back (unit);
    const unsigned *end = lits + size;
    for (const unsigned *p = lits; p != end; p++)
      pc.literals.push_back (internal->citten2lit (*p)); // conversion
    proof_clauses.push_back (pc);
    assert (proof);
    proof->add_derived_clause (pc.id, true, pc.literals, pc.chain);
  } else {
    internal->assign_unit (unit);
    for (const auto & pc : proof_clauses) {
      proof->delete_clause (pc.id, true, pc.literals);
    }
    proof_clauses.clear ();
  }
}

// extract lrat proofs for relevant clauses
//
static void traverse_one_sided_core_lemma_with_lrat (void *state, unsigned cid,
                                                      unsigned id, bool learned,
                                           size_t size, const unsigned *lits,
                                           size_t chain_size, const unsigned *chain) {
  definition_extractor *extractor = (definition_extractor *) state;
  Eliminator *eliminator = extractor->eliminator;
  Internal *internal = extractor->internal;
  Proof *proof = internal->proof;
  const int unit = extractor->unit;
  const vector<Clause*> &clauses0 = extractor->clauses[0];
  const vector<Clause*> &clauses1 = extractor->clauses[1];
  vector<proof_clause> &proof_clauses = eliminator->proof_clauses;
  if (!learned) {  // remember clauses for mapping to kitten internal
    assert (size);
    assert (!chain_size);
    proof_clause pc;
    pc.cid = cid;
    pc.learned = false;
    const size_t size_clauses0 = clauses0.size ();
    assert (size_clauses0 <= UINT_MAX);
    if (id < size_clauses0) {
      pc.id = clauses0[id]->id;
    } else {
      unsigned tmp = id - size_clauses0;
#ifndef NDEBUG
      const size_t size_clauses1 = clauses1.size ();
      assert (size_clauses1 <= UINT_MAX);
      assert (tmp < size_clauses1);
#endif
      pc.id = clauses1[tmp]->id;
    }
    proof_clauses.push_back (pc);
  } else {  // actually add to proof
    assert (chain_size);
    if (size) {
      proof_clause pc;
      pc.id = ++(internal->clause_id);
      pc.cid = cid;
      pc.learned = true;
      pc.literals.push_back (unit);
      const unsigned *end = lits + size;
      for (const unsigned *p = lits; p != end; p++)
        pc.literals.push_back (internal->citten2lit (*p)); // conversion
      for (const unsigned *p = chain + chain_size; p != chain; p--) {
        uint64_t id = 0;
        for (const auto & cpc : proof_clauses) {
          if (cpc.cid == *(p-1)) {
            id = cpc.id;
            break;
          }
        }
        assert (id);
        pc.chain.push_back (id);
      }
      proof_clauses.push_back (pc);
      assert (proof);
      proof->add_derived_clause (pc.id, true, pc.literals, pc.chain);
    } else {  // learn unit finish proof
      assert (internal->lrat_chain.empty ());
      for (const unsigned *p = chain + chain_size; p != chain; p--) {
        uint64_t id = 0;
        for (const auto & cpc : proof_clauses) {
          if (cpc.cid == *(p-1)) {
            id = cpc.id;
            break;
          }
        }
        assert (id);
        internal->lrat_chain.push_back (id);
      }
      internal->assign_unit (unit);
      assert (internal->lrat_chain.empty ());
      for (const auto & pc : proof_clauses) {
        if (pc.learned)
          proof->delete_clause (pc.id, true, pc.literals);
      }
      proof_clauses.clear ();
    }
  }
}

static bool ignore_negative (void *state, unsigned id) {
  definition_extractor *extractor = (definition_extractor *) state;
  const vector<Clause*> &clauses0 = extractor->clauses[0];
  const size_t size_clauses0 = clauses0.size ();
  assert (size_clauses0 <= UINT_MAX);
  const vector<Clause*> &clauses1 = extractor->clauses[1];
  const size_t size_clauses1 = clauses1.size ();
  if (id >= size_clauses0 + size_clauses1) {
    unsigned tmp = id - size_clauses0 - size_clauses1;
    assert (tmp < extractor->implicants.size ());
    return extractor->implicants[tmp][0] == extractor->lit;
  }
  if (id < size_clauses0)
    return true;
#ifndef NDEBUG
  unsigned tmp = id - size_clauses0;
  assert (size_clauses1 <= UINT_MAX);
  assert (tmp < size_clauses1);
#endif
  return false;
}

static void add_implicant (void *state, int side, size_t size,
                                const unsigned *lits) {
  definition_extractor *extractor = (definition_extractor *) state;
  const unsigned id = extractor->clauses[0].size () + extractor->clauses[1].size ()
                                                 + extractor->implicants.size ();
  vector<int> implicant;
  const int pivot = extractor->lit;
  implicant.push_back (side ? pivot : -pivot);
  const auto end = lits + size;
  for (auto q = lits; q != end; q++) {
    implicant.push_back (extractor->internal->citten2lit (*q));
  }
  extractor->implicants.push_back (implicant);
  kitten_clause_with_id_and_exception (extractor->internal->citten, id, size, lits, INVALID); 
}

} // end extern C


// Code ported from kissat. Kitten (and kissat) use unsigned representation
// for literals whereas CaDiCaL uses signed representation. Conversion is
// necessary for communication using lit2citten and citten2lit.
// This code is called in elim and kitten is initialized beforehand.
// To avoid confusion all cadical interal definitions with kitten are called
// citten.
//
void Internal::find_definition (Eliminator &eliminator, int lit) {
  if (!opts.elimdef)
    return;
  if (unsat)
    return;
  if (val (lit))
    return;
  if (!eliminator.gates.empty ()) return;
  assert (!val (lit));
  assert (!level);
  assert (citten);
  const int not_lit = -lit;
  definition_extractor extractor;
  extractor.lit = lit;
  extractor.clauses[0] = occs (lit);
  extractor.clauses[1] = occs (not_lit);
  extractor.eliminator = &eliminator;
  extractor.internal = internal;
  citten_clear_track_log_terminate ();
  unsigned exported = 0;
  for (unsigned sign = 0; sign < 2; sign++) {
    const unsigned except = sign ? lit2citten (not_lit) : lit2citten (lit);
    for (auto c : extractor.clauses[sign]) {
      // to avoid copying the literals of c in their unsigned
      // representation we instead implement the translation in kitten
      if (!c->garbage) {
        LOG (c, "adding to kitten");
        citten_clause_with_id_and_exception (citten, exported, c->size,
                                             c->literals, except);
      }
      exported++;
    }
  }
  stats.definitions_checked++;
  const size_t limit = opts.elimdefticks;
  kitten_set_ticks_limit (citten, limit);
  int primeround = 1;
BEGIN:
  int status = kitten_solve (citten);
  if (!exported) goto ABORT;
  if (status == 20) {
    LOG ("sub-solver result UNSAT shows definition exists");
    uint64_t learned;
    unsigned reduced = kitten_compute_clausal_core (citten, &learned);
    LOG ("1st sub-solver core of size %u original clauses out of %u",
         reduced, exported);
    for (int i = 2; i <= opts.elimdefcores; i++) {
      kitten_shrink_to_clausal_core (citten);
      kitten_shuffle_clauses (citten);
      kitten_set_ticks_limit (citten, 10 * limit);
      int tmp = kitten_solve (citten);
      assert (!tmp || tmp == 20);
      if (!tmp) {
        LOG ("aborting core extraction");
        goto ABORT;
      }
#ifndef NDEBUG
      unsigned previous = reduced;
#endif
      reduced = kitten_compute_clausal_core (citten, &learned);
      LOG ("%d sub-solver core of size %u original clauses out of %u", i,
           reduced, exported); // TODO happy ordinal
      assert (reduced <= previous);
#if not defined(LOGGING) && defined(NDEBUG)
      (void) reduced;
#endif
    }
    stats.definitions_extracted++;
    eliminator.gatetype = DEF;
    eliminator.definition_unit = 0;
    kitten_traverse_core_ids (citten, &extractor, traverse_definition_core);
    assert (eliminator.definition_unit);
    int unit = 0;
    if (eliminator.definition_unit == 2) {
      unit = not_lit;
    } else if (eliminator.definition_unit == 1)
      unit = lit;

    if (unit) {
      stats.definition_units++;
      VERBOSE (2, "one sided core "
                  "definition extraction yields "
                  "failed literal");
      if (proof) {
        if (lrat) {
          extractor.unit = unit;
          kitten_trace_core (citten, &extractor,
                              traverse_one_sided_core_lemma_with_lrat);
        } else {
          extractor.unit = unit;
          kitten_traverse_core_clauses (citten, &extractor,
                                        traverse_one_sided_core_lemma);
        }
      } else
        assign_unit (unit);
      elim_propagate (eliminator, unit);
    }
  } else if (status == 10 && opts.elimdefprime) {
    if (primeround > opts.elimdefprimeround) goto ABORT;
    primeround++;
    int side = kitten_compute_prime_implicant (citten, &extractor, ignore_negative);
    if (side == -1) goto ABORT;
    stats.definition_prime++;
    kitten_add_prime_implicant (citten, &extractor, side, add_implicant);
    goto BEGIN;
  } else {
  ABORT:
    LOG ("sub-solver failed to show that definition exists");
    eliminator.prime_gates.clear ();
  }
  stats.definition_ticks += kitten_current_ticks (citten);
  return;
}

void Internal::delete_all_redundant_def (int blit) {
  const Occs &ps = roccs (blit);
  for (const auto &c : ps) {
    if (c->garbage) continue;
    mark_garbage (c);
  }
}

void Internal::add_definition_blocking_clauses (Eliminator &eliminator) {
  if (!eliminator.prime_gates.size ()) return;
  if (!opts.elimdefprimeadd) return;
  int pivot = eliminator.prime_gates[0][0];
  delete_all_redundant_def (-pivot);
  for (auto &bc : eliminator.prime_gates) {
    if (bc[0] != pivot) {
      assert (bc[0] == -pivot);
      delete_all_redundant_def (pivot);
      break;
    }
  }
  for (auto &bc : eliminator.prime_gates) {
    assert (clause.empty ());
    clause.swap (bc);
    Clause *res = new_hyper_ternary_resolved_clause (true);
    stats.definition_prime_added++;
    for (const auto &lit : *res)
      roccs (lit).push_back (res);
    // elim_update_added_clause (eliminator, res);
    clause.clear ();
  }
  eliminator.prime_gates.clear ();
}

} // namespace CaDiCaL
