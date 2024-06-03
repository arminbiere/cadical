#include "internal.hpp"

namespace CaDiCaL {

#define INVALID_LIT UINT_MAX

// functions below are passed to kitten
//
struct equivalence_extractor {
  unsigned pivot;
  unsigned other;
  Eliminator *eliminator;
  vector<Clause*> clauses[2];
};

struct lemma_extractor {
  Eliminator *eliminator;
  Internal *internal;
  int pivot;
  int other;
};

struct lrat_extractor {
  Eliminator *eliminator;
  Internal *internal;
  vector<Clause*> clauses[2];
  int pivot;
  int other;
};

extern "C" {

// extracts relevant learned clauses from kissat for drat proofs
//
static void traverse_core_lemma (void *state, bool learned,
                                 size_t size,
                                 const unsigned *lits) {
  if (!learned)
    return;
  lemma_extractor *extractor = (lemma_extractor *) state;
  Eliminator *eliminator = extractor->eliminator;
  Internal *internal = extractor->internal;
  Proof *proof = internal->proof;
  const int pivot = extractor->pivot;
  const int best = extractor->other;
  vector<proof_clause> &proof_clauses = eliminator->proof_clauses;
  if (size) {
    proof_clause pc;
    pc.id = ++(internal->clause_id);
    pc.literals.push_back (-pivot);
    pc.literals.push_back (-best);
    const unsigned *end = lits + size;
    for (const unsigned *p = lits; p != end; p++)
      pc.literals.push_back (internal->citten2lit (*p)); // conversion
    proof_clauses.push_back (pc);
    assert (proof);
    proof->add_derived_clause (pc.id, true, pc.literals, pc.chain);
  } else {
    internal->clause.push_back (-pivot);
    internal->clause.push_back (-best);
    Clause *res = internal->new_resolved_irredundant_clause ();
    internal->clause.clear ();
    res->gate = true;
    eliminator->gates.push_back (res);
    internal->elim_update_added_clause (*eliminator, res);
    Clause *d = 0;
    const Occs &ps = internal->occs (pivot);
    for (const auto &e : ps) {
      if (e->garbage)
        continue;
      const int other =
          internal->second_literal_in_binary_clause (*eliminator, e, pivot);
      if (other == best) {
        d = e;
        break;
      }
    }
    assert (d);
    d->gate = true;
    eliminator->gates.push_back (d);
    for (const auto & pc : proof_clauses) {
      proof->delete_clause (pc.id, true, pc.literals);
    }
    proof_clauses.clear ();
  }
}

static int citten_terminate (void *data) {
  return ((Terminator *) data)->terminate ();
}

// extract lrat proofs for relevant clauses
//
static void traverse_core_lemma_with_lrat (void *state, unsigned cid,
                                           unsigned id, bool learned,
                                           size_t size, const unsigned *lits,
                                           size_t chain_size, const unsigned *chain) {
  lrat_extractor *extractor = (lrat_extractor *) state;
  Eliminator *eliminator = extractor->eliminator;
  Internal *internal = extractor->internal;
  Proof *proof = internal->proof;
  const int pivot = extractor->pivot;
  const int best = extractor->other;
  vector<Clause*> clauses0 = extractor->clauses[0];
  vector<Clause*> clauses1 = extractor->clauses[1];
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
      pc.literals.push_back (pivot);
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
      internal->assign_unit (pivot);
      assert (internal->lrat_chain.empty ());
      for (const auto & pc : proof_clauses) {
        if (pc.learned)
          proof->delete_clause (pc.id, true, pc.literals);
      }
      proof_clauses.clear ();
    }
  }
}

} // end extern C

bool Internal::find_next_eq (Eliminator &eliminator, int pivot, int best) {
  kitten_clear (citten);
  equivalence_extractor extractor;
  extractor.pivot = lit2citten (pivot); // here the conversion happens.
  extractor.other = lit2citten (best); // here the conversion happens.
  extractor.clauses[0] = occs (-pivot);
  extractor.clauses[1] = occs (-best);
  extractor.eliminator = &eliminator;
#ifdef LOGGING
  if (opts.log)
    kitten_set_logging (citten);
#endif
  kitten_track_antecedents (citten);
  if (external->terminator)
    kitten_set_terminator (citten, external->terminator, citten_terminate);
  unsigned exported = 0;
  for (unsigned sign = 0; sign < 2; sign++) {
    for (auto c : extractor.clauses[sign]) {
      // to avoid copying the literals of c in their unsigned
      // representation we instead implement the translation in kitten
      if (!c->garbage)
        citten_clause_with_id_and_equivalence (citten, exported, c->size,
                                             c->literals, extractor.pivot,
                                             extractor.other);
      exported++;
    }
  }
  stats.equivalences_checked++;
  const size_t limit = opts.elimciteqticks;
  kitten_set_ticks_limit (citten, limit);
  int status = kitten_solve (citten);
  if (status == 10 && false) {
    signed char citten_vals[max_var+1] {};
    for (const auto & lit : vars) {
      citten_vals[lit] = kitten_signed_value (citten, lit);  // kitten converts
    }
    for (const auto & ulit : vars) {
      const auto lit = -ulit * citten_vals[ulit];
      if (!lit) continue;
      vector<Clause*> clauses = occs (lit);
      for (auto c : clauses) {
        if (!c->garbage) continue;
        bool sat = false;
        for (auto l : *c) {
          if (citten_vals[l] >= 0) {
            sat = true;
            break;
          }
        }
        if (sat) continue;
        citten_clause_with_id_and_equivalence (citten, exported, c->size,
                                             c->literals, extractor.pivot,
                                             extractor.other);
      }
    }
    status = kitten_solve (citten);
  }
  if (status == 20) {
    LOG ("sub-solver result UNSAT shows equivalene exists");
    uint64_t learned;
    unsigned reduced = kitten_compute_clausal_core (citten, &learned);
    LOG ("1st sub-solver core of size %u original clauses out of %u",
         reduced, exported);
#ifndef LOGGING
    (void) reduced;
#endif
    stats.equivalences_extracted++;
    if (proof) { // TODO
      if (lrat) {
        lrat_extractor extractor;
        extractor.pivot = pivot;
        extractor.other = best;
        extractor.eliminator = &eliminator;
        extractor.internal = internal;
        extractor.clauses[0] = occs (pivot);
        extractor.clauses[1] = occs (-pivot);
        kitten_trace_core (citten, &extractor,
                            traverse_core_lemma_with_lrat);
      } else {
        lemma_extractor extractor;
        extractor.pivot = pivot;
        extractor.other = best;
        extractor.eliminator = &eliminator;
        extractor.internal = internal;
        kitten_traverse_core_clauses (citten, &extractor,
                                      traverse_core_lemma);
      }
    } else {
      clause.push_back (-pivot);
      clause.push_back (-best);
      Clause *res = new_resolved_irredundant_clause ();
      clause.clear ();
      res->gate = true;
      eliminator.gates.push_back (res);
      elim_update_added_clause (eliminator, res);
      Clause *d = 0;
      const Occs &ps = occs (pivot);
      for (const auto &e : ps) {
        if (e->garbage)
          continue;
        const int other =
            second_literal_in_binary_clause (eliminator, e, pivot);
        if (other == best) {
          d = e;
          break;
        }
      }
      assert (d);
      d->gate = true;
      eliminator.gates.push_back (d);
    }
    return true;
  }
  return false;
}

// Code ported from kissat. Kitten (and kissat) use unsigned representation
// for literals whereas CaDiCaL uses signed representation. Conversion is
// necessary for communication using lit2citten and citten2lit.
// This code is called in elim and kitten is initialized beforehand.
// To avoid confusion all cadical interal definitions with kitten are called
// citten.
//
void Internal::find_citten_eq (Eliminator &eliminator, int pivot) {
  if (!opts.elimciteq)
    return;
  if (unsat)
    return;
  if (val (pivot))
    return;
  if (!eliminator.gates.empty ()) return;
  
  assert (!val (pivot));
  assert (!level);
  assert (citten);
  
  mark_binary_literals (eliminator, pivot);
  if (unsat || val (pivot)) {
    unmark_binary_literals (eliminator);
    return;
  }
  if (eliminator.marked.empty ()) {
    LOG ("equivalence with kitten failed due to no candidates");
    return;
  }

  int round = 0;
  for (const auto & best : eliminator.marked) {
    if (find_next_eq (eliminator, pivot, best)) break;
    else if (round == opts.elimciteqround) break;
    round++;
  }
  
  // int best = 0;
  // int64_t size = 0;
  // for (const auto & other : eliminator.marked) {
  //   assert (!val (other));
  //   const int64_t nsl = noccs (pivot);
  //   if (nsl <= size) continue;
  //   size = nsl;
  //   best = other;
  // }
  // assert (best);

  unmark_binary_literals (eliminator);
}

} // namespace CaDiCaL
