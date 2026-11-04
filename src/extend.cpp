#include "internal.hpp"
#include "util.hpp"

// The extension data allows to reconstruct a satisfying assignment for the
// original formula after removing weakened clauses. This was pioneered by
// Niklas Soerensson in MiniSAT and for instance is described in our
// inprocessing paper, published at IJCAR'12. The first few functions are
// used to add clauses to the extension.
//
// For clauses with a single witness literal, we separate the witness
// information from the clause data. Restoration and extension are then
// driven by the 'witness_data' stack, which stores:
//    wit | blit | idx
// Here, 'wit' is the witness literal, 'blit' is a blocking literal, and
// 'idx' is the index of the first element of the corresponding clause
// record in the 'clause_data' stack. Separating witness information from
// clause data improves the average-case runtime of model extension and
// clause restoration.
//
// Clauses with multiple witness literals, i.e., a witness cube, are stored
// differently. Since the blocking literal of a single-witness clause cannot
// be zero, we use the record
//    0 | 0 | idx
// in 'witness_data' to represent a witness cube stack. Here, 'idx' is the
// index of the first element of the corresponding record in 'clause_data'.
// The record consists of the witness cube, terminated by '0', followed by
// one or more clauses sharing that witness cube. The sequence of clauses is
// itself terminated by '0'. Each clause is encoded as usual, with all its
// literals stored explicitly. The clauses within a witness cube stack are
// unordered with respect to the weakening timeline: since they belong to
// the same weakening event, their order of examination during extension and
// restoration does not matter.
//
// Clause Encoding:
// Each clause record in 'clause_data' begins with an encoded size field.
// This field stores the number of literals as well as additional metadata.
// If the number of literals is less than 2^29, the most significant bit is
// set, allowing the next two bits to be used as flags:
//  bit 30: The witness is a subset of the clause and is not stored
//  explicitly
//          as a literal.
//  bit 29: The clause ID fits into 32 bits.
// This allows a more compact representation in the common case.
//
/* --------------------------------------------------------------------------
 */
namespace CaDiCaL {

static constexpr uint32_t CLAUSE_SMALL = 1u << 31;
static constexpr uint32_t EMBEDDED = 1u << 30;
static constexpr uint32_t ID_LONG = 1u << 29;
static constexpr uint32_t SIZE_MASK = (1u << 29) - 1;

static inline void decode_size_field (const int size_field,
                                      bool &wit_embedded, bool &id_long,
                                      unsigned &other_lits_size) {
  // In the binary clause case size can be zero but then we have the witness
  // implicit and have set the corresponding bit.
  assert (size_field);

  const uint32_t encoded = static_cast<uint32_t> (size_field);
  const bool clause_small = encoded & CLAUSE_SMALL;

  wit_embedded = clause_small && (encoded & EMBEDDED);
  id_long = !clause_small || (encoded & ID_LONG);
  other_lits_size = clause_small ? (encoded & SIZE_MASK) : encoded;
}

static inline int64_t decode_id (vector<int>::const_iterator p,
                                 const bool id_long) {
  if (!id_long)
    return static_cast<uint32_t> (*(p + 1));
  const uint64_t upper = static_cast<uint32_t> (*(p + 1));
  const uint64_t lower = static_cast<uint32_t> (*(p + 2));
  return static_cast<int64_t> ((upper << 32) | lower);
}

void External::push_clause_on_extension (int iwit, Clause *c) {
  assert (iwit);
  LOG (c, "pushing on witness data");

  const unsigned size = c->size;

  internal->stats.weakened++;
  internal->stats.weakened_lengths += size;

  const int ewit = internal->externalize (iwit);
  assert (ewit);

  // Remember the index of the first size field.
  clause_data.push_back (0); // Will be updated in the end.
  const uint64_t idx = clause_data.size () - 1;

  const bool compactable = size < (1u << 29);
  const bool id_long = c->id > UINT32_MAX;

  const uint32_t idu = static_cast<uint32_t> (c->id >> 32);
  const uint32_t idl = static_cast<uint32_t> (c->id);
  // If we cannot flag since the clause is too large or the id is just too
  // long we push both parts.
  if (!compactable || id_long) {
    LOG ("pushing long id %" PRId64, c->id);
    clause_data.push_back (static_cast<int> (idu));
    clause_data.push_back (static_cast<int> (idl));
  } else {
    assert (!idu);
    LOG ("pushing compact id %" PRId64, c->id);
    clause_data.push_back (static_cast<int> (idl));
  }

  // Now we will push the literals.
  // We will skip the witness literal if possible, i.e. if the clause is
  // compactable and the witness is included in the clause.
  int blit = 0;
  bool embedded = false;
  for (const auto &lit : *c) {
    const int elit = internal->externalize (lit);

    if (elit == ewit) {
      if (compactable) { // Do not store the witness literal.
        embedded = true;
        continue;
      }
    } else if (!blit) { // Also pick some blit. It is stored on
                        // witness_data.
      blit = elit;
      continue;
    }

    clause_data.push_back (elit);
  }
  assert (blit);

  // Finally we update the size fields accordingly.
  uint32_t updated_size =
      c->size - 1; // Blocking literal is stored elsewhere.
  if (embedded) {
    updated_size--;
    updated_size |= EMBEDDED;
  }
  if (compactable) {
    updated_size |= CLAUSE_SMALL;
    if (id_long)
      updated_size |= ID_LONG;
  }
  // Update the size field and push the terminating size field.
  clause_data[idx] = static_cast<int> (updated_size);

  if (!marked (witness, ewit)) {
    LOG ("marking as witness %d (external)", ewit);
    mark (witness, ewit);
  }

  LOG ("pushing witness %d and blocking literal %d (external)", ewit, blit);
  witness_data.push_back ({ewit, blit, idx});
}

void External::push_clause_on_extension (const int64_t id, int iwit,
                                         const vector<int> &c) {
  assert (iwit);
  assert (id > 0);
  assert (c.size ());

  LOG (c.begin (), c.end (), "pushing on witness data clause[%" PRId64 "] ",
       id);
  internal->stats.weakened++;

  const unsigned size = c.size ();

  internal->stats.weakened_lengths += size;

  const int ewit = internal->externalize (iwit);
  assert (ewit);

  // Remember the index of the first size field.
  clause_data.push_back (0); // Will be updated in the end.
  const uint64_t idx = clause_data.size () - 1;

  const bool compactable = size < (1u << 29);
  const bool id_long = id > UINT32_MAX;

  const uint32_t idu = static_cast<uint32_t> (id >> 32);
  const uint32_t idl = static_cast<uint32_t> (id);
  // If we cannot flag since the clause is too large or the id is just too
  // long we push both parts.
  if (!compactable || id_long) {
    LOG ("pushing long id %" PRId64, id);
    clause_data.push_back (static_cast<int> (idu));
    clause_data.push_back (static_cast<int> (idl));
  } else {
    assert (!idu);
    LOG ("pushing compact id %" PRId64, id);
    clause_data.push_back (static_cast<int> (idl));
  }

  // Now we will push the literals.
  // We will skip the witness literal if possible, i.e. if the clause is
  // compactable and the witness is included in the clause.
  int blit = 0;
  bool embedded = false;
  for (const auto &lit : c) {
    const int elit = internal->externalize (lit);

    if (elit == ewit) {
      if (compactable) { // Do not store the witness literal.
        embedded = true;
        continue;
      }
    } else if (!blit) { // Also pick some blit. It is stored on
                        // witness_data.
      blit = elit;
      continue;
    }

    clause_data.push_back (elit);
  }
  assert (blit);

  // Finally we update the size fields accordingly.
  uint32_t updated_size = size - 1; // Blocking literal is stored elsewhere.
  if (embedded) {
    updated_size--;
    updated_size |= EMBEDDED;
  }
  if (compactable) {
    updated_size |= CLAUSE_SMALL;
    if (id_long)
      updated_size |= ID_LONG;
  }
  // Update the size field and push the terminating size field.
  clause_data[idx] = static_cast<int> (updated_size);

  if (!marked (witness, ewit)) {
    LOG ("marking as witness %d (external)", ewit);
    mark (witness, ewit);
  }

  LOG ("pushing witness %d and blocking literal %d (external)", ewit, blit);
  witness_data.push_back ({ewit, blit, idx});
}

void External::push_binary_clause_on_extension (int64_t id, int iwit,
                                                int other) {
  LOG ("pushing on witness data binary clause[%" PRId64 "] %d %d", id,
       other, iwit);

  internal->stats.weakened++;
  internal->stats.weakened_lengths += 2;

  const int ewit = internal->externalize (iwit);
  assert (ewit);

  // Remember the index of the first size field.
  clause_data.push_back (0); // Will be updated in the end.
  const uint64_t idx = clause_data.size () - 1;

  const bool id_long = id > UINT32_MAX;
  const uint32_t idu = static_cast<uint32_t> (id >> 32);
  const uint32_t idl = static_cast<uint32_t> (id);

  if (id_long) {
    clause_data.push_back (static_cast<int> (idu));
    clause_data.push_back (static_cast<int> (idl));
  } else {
    assert (!idu);
    clause_data.push_back (static_cast<int> (idl));
  }

  // No literal will be pushed. Both literals are on witness_data.

  uint32_t updated_size = 0;
  updated_size |= EMBEDDED;
  updated_size |= CLAUSE_SMALL;

  if (id_long)
    updated_size |= ID_LONG;

  clause_data[idx] = static_cast<int> (updated_size);

  if (!marked (witness, ewit)) {
    LOG ("marking as witness %d (external)", ewit);
    mark (witness, ewit);
  }

  const int blit = internal->externalize (other);
  LOG ("pushing witness %d and blocking literal %d (external)", ewit, blit);
  witness_data.push_back ({ewit, blit, idx});
}

/* --------------------------------------------------------------------------
 */
// The procedure for creating a witness cube stack is as follows:
// First, 'create_cube_stack' creates a cube stack for the given witness
// cube. Then, one or more clauses are added by repeatedly calling
// 'push_cube_clause'. Once all clauses have been added, the cube stack is
// terminated by calling 'terminate_cube_stack'.

void External::create_cube_stack (const vector<int> &iwit_cube) {
  LOG (iwit_cube, "pushing to clause_data cube ");

  const uint64_t idx = clause_data.size ();

  for (const auto &iwit : iwit_cube) {
    const int ewit = internal->externalize (iwit);
    assert (ewit);

    clause_data.push_back (ewit);

    if (!marked (witness, ewit))
      mark (witness, ewit);
  }
  clause_data.push_back (0); // End of witness cube.

  witness_data.push_back ({0, 0, idx});
}

void External::push_cube_clause (Clause *c) {
  LOG (c, "pushing on witness data");

  const unsigned size = c->size;

  internal->stats.weakened++;
  internal->stats.weakened_cube_cls++;
  internal->stats.weakened_lengths += size;

  clause_data.push_back (0); // Will be updated in the end.
  const uint64_t idx = clause_data.size () - 1;

  const bool compactable = size < (1u << 29);
  const bool id_long = c->id > UINT32_MAX;

  const uint32_t idu = static_cast<uint32_t> (c->id >> 32);
  const uint32_t idl = static_cast<uint32_t> (c->id);
  // If we cannot flag since the clause is too large or the id is just too
  // long we push both parts.
  if (!compactable || id_long) {
    LOG ("pushing long id %" PRId64, c->id);
    clause_data.push_back (static_cast<int> (idu));
    clause_data.push_back (static_cast<int> (idl));
  } else {
    assert (!idu);
    LOG ("pushing compact id %" PRId64, c->id);
    clause_data.push_back (static_cast<int> (idl));
  }

  for (const auto &lit : *c) {
    const int elit = internal->externalize (lit);
    clause_data.push_back (elit);
  }

  uint32_t updated_size = size;

  if (compactable) {
    updated_size |= CLAUSE_SMALL;
    if (id_long)
      updated_size |= ID_LONG;
  }
  clause_data[idx] = static_cast<int> (updated_size);
}

void External::terminate_cube_stack () { clause_data.push_back (0); }

void External::create_cube_stack_and_push_external_clause (
    const vector<int> &clause, const vector<int> &ewit_cube, int64_t id) {

  // first push the witness cube
  const uint64_t cube_idx = clause_data.size ();
  for (const auto &elit : ewit_cube) {
    assert (elit != INT_MIN && elit);
    assert (abs (elit) <= max_var);
    int eidx = abs (elit);
    int ilit = e2i.find_or_default (eidx, 0);
    if (!ilit) {
      init (eidx);
      assert (e2i.find_or_default (eidx, 0));
      ilit = e2i.find (eidx).second;
    }
    assert (ilit && ilit != INT_MIN);
    clause_data.push_back (elit);
    mark (witness, elit);
  }
  clause_data.push_back (0);

  // then push the clause.
  clause_data.push_back (0); // Updated in the end.
  const uint64_t first_size_field = clause_data.size () - 1;

  const unsigned size = clause.size ();
  const bool compactable = size < (1u << 29);
  const bool id_long = id > UINT32_MAX;

  const uint32_t idu = static_cast<int> (id >> 32);
  const uint32_t idl = (id & (((int64_t) 1 << 32) - 1));

  if (!compactable || id_long) {
    LOG ("pushing long id %" PRId64, id);
    clause_data.push_back (static_cast<int> (idu));
    clause_data.push_back (static_cast<int> (idl));
  } else {
    LOG ("pushing compact id %" PRId64, id);
    clause_data.push_back (static_cast<int> (idl));
  }

  for (const auto &elit : clause) {
    assert (elit != INT_MIN);
    assert (abs (elit) <= max_var);
    int eidx = abs (elit);
    int ilit = e2i.find_or_default (eidx, 0);
    if (!ilit) {
      init (eidx);
      assert (e2i.find_or_default (eidx, 0));
      ilit = e2i.find (eidx).second;
    }
    assert (ilit && ilit != INT_MIN);
    clause_data.push_back (elit);
  }

  // Finally we update the size fields accordingly;
  uint32_t updated_size = clause.size ();
  if (compactable) {
    updated_size |= CLAUSE_SMALL;
    if (id_long)
      updated_size |= ID_LONG;
  }

  clause_data[first_size_field] = static_cast<int> (updated_size);
  clause_data.push_back (0); // Witness cube stack terminator.

  witness_data.push_back ({0, 0, cube_idx});
}

void External::push_external_clause_on_extension (const vector<int> &c,
                                                  const vector<int> &w,
                                                  int64_t id) {
  assert (id);
  assert (w.size () == 1);
  const int ewit = w[0];
  assert (ewit != INT_MIN && ewit);
  assert (abs (ewit) <= max_var);

  int eidx = abs (ewit);
  int ilit = e2i.find_or_default (eidx, 0);
  if (!ilit) {
    init (eidx);
    assert (e2i.find_or_default (eidx, 0));
    ilit = e2i.find (eidx).second;
  }
  assert (ilit && ilit != INT_MIN);

  // Remember the index of the first size field.
  clause_data.push_back (0); // Will be updated in the end.
  const uint64_t idx = clause_data.size () - 1;

  const unsigned size = c.size ();
  const bool compactable = size < (1u << 29);
  const bool id_long = id > UINT32_MAX;

  const uint32_t idu = static_cast<uint32_t> (id >> 32);
  const uint32_t idl = static_cast<uint32_t> (id);

  if (!compactable || id_long) {
    LOG ("pushing long id %" PRId64, id);
    clause_data.push_back (static_cast<int> (idu));
    clause_data.push_back (static_cast<int> (idl));
  } else {
    assert (!idu);
    LOG ("pushing compact id %" PRId64, id);
    clause_data.push_back (static_cast<int> (idl));
  }

  int blit = 0;
  bool embedded = false;
  for (const auto &elit : c) {
    assert (elit != INT_MIN);
    assert (abs (elit) <= max_var);
    int eidx = abs (elit);
    int ilit = e2i.find_or_default (eidx, 0);
    if (!ilit) {
      init (eidx);
      assert (e2i.find_or_default (eidx, 0));
      ilit = e2i.find (eidx).second;
    }
    assert (ilit && ilit != INT_MIN);

    if (elit == ewit) {
      if (compactable) {
        embedded = true;
        continue;
      }
    } else if (!blit) {
      blit = elit;
      continue;
    }

    clause_data.push_back (elit);
  }
  assert (blit);

  uint32_t updated_size = size - 1;
  if (embedded) {
    updated_size--;
    updated_size |= EMBEDDED;
  }
  if (compactable) {
    updated_size |= CLAUSE_SMALL;
    if (id_long)
      updated_size |= ID_LONG;
  }

  // Update the size field and push the terminating size field.
  clause_data[idx] = static_cast<int> (updated_size);
  if (!marked (witness, ewit)) {
    LOG ("marking as witness %d (external)", ewit);
    mark (witness, ewit);
  }

  LOG ("pushing witness %d and blocking literal %d (external)", ewit, blit);
  witness_data.push_back ({ewit, blit, idx});
}

/*------------------------------------------------------------------------*/
// the calls to init are used in the copy test, should never trigger during
// actual solver runtime.
void External::push_external_clause_and_witness_on_extension (
    const vector<int> &c, const vector<int> &w, int64_t id) {
  assert (id);
  if (w.size () == 1)
    push_external_clause_on_extension (c, w, id);
  else
    create_cube_stack_and_push_external_clause (c, w, id);
}

/*------------------------------------------------------------------------*/
// This is the actual extension process. We traverse 'witness_data'
// backward and extend the corresponding clauses.
//
// For each clause, we first check whether its witness is assigned.
// If so, the clause is satisfied and we can skip examining its literals.
// We also push a blocking literal for this purpose: we only examine
// the clause's literals if neither the witness nor the blocking literal
// is satisfied.
// For a witness cube stack, we first check whether the witness cube
// is satisfied. If so, we can skip all clauses on this stack.
// Otherwise, we examine the clauses sequentially by traversing the
// stack. Once we find a clause that is unsatisfied by the current
// assignment, we assign the witness cube and can skip the remaining clauses
// on this stack.
//

void External::extend_cube_stack (uint32_t ss_idx, ExtendStats &stats) {
  LOG ("extending cube stack at index %u", ss_idx);

  bool satisfied = true;
  auto q = clause_data.begin () + ss_idx;

  // first check the cube for being satisfied. Also check if this stack has
  // been already been scheduled for extension.
  LOG ("witness cube: ");
  while (*q) {
    LOG ("%d", *q);
    const int ewit = *q++;
    // some witness falsified or unassigned
    if (ival (ewit) != ewit) {
      satisfied = false;
      break;
    }
  }
  while (*q) {
    LOG ("%d", *q);
    q++;
  }

  if (satisfied) {
    LOG ("witness cube already satisfied.");
    stats.extend_blocked++;
    return;
  }

  // The witness cube is not fully assigned. Therefore we need to check for
  // unsatisfied clauses.
  ++q; // Skip the cube terminator.
  bool assign_witness = false;
  assert (*q);
  while (*q != 0) {
    stats.clauses_read++;

    bool wit_embedded, id_long;
    unsigned other_lits_size;
    decode_size_field (*q, wit_embedded, id_long, other_lits_size);
    assert (!wit_embedded);
    assert (other_lits_size);

    q += (id_long ? 3 : 2); // q points to the first literal.
    auto end_of_lits = q + other_lits_size;
    bool satisfied = false;

    while (q != end_of_lits) {
      const int elit = *q;
      if (!satisfied && ival (elit) == elit)
        satisfied = true;
      ++q;
    }

    // assign the cube.
    if (!satisfied) {
      assign_witness = true;
      break;
    }
  }

  if (assign_witness) {
    q = clause_data.begin () + ss_idx;
    while (*q) {
      const int ewit = *q++;
      if (ival (ewit) == ewit)
        continue;
      LOG ("flipping witness literal %d", ewit);
      assert (ewit);
      assert (ewit != INT_MIN);
      size_t idx = abs (ewit);
      if (idx >= vals.size ())
        vals.resize (idx + 1, false);
      vals[idx] = !vals[idx];
      internal->stats.extended++;
#ifndef QUIET
      stats.flipped++;
#endif
    }
  }
}

void External::extend () {
  assert (!extended);
  PROFILE_SCOPE (extend);
  internal->stats.extensions++;

  PHASE ("extend", internal->stats.extensions,
         "mapping internal %d assignments to %d assignments",
         internal->max_var, max_var);

  ExtendStats stats = {};

  // Copy the internal assignment into an external one
  for (unsigned i = 1; i <= (unsigned) max_var; i++) {
    const int ilit = e2i.find (i).second;
    if (!ilit)
      continue;
    if (i >= vals.size ())
      vals.resize (i + 1, false);
    vals[i] = (internal->val (ilit) > 0);
#ifndef QUIET
    stats.updated++;
#endif
  }

  auto p = witness_data.end ();
  auto begin = witness_data.begin ();

  while (p != begin) {
    const WitnessEntry &entry = *--p;
    const uint64_t idx = entry.idx;
    const int blit = entry.blit;
    const int ewit = entry.ewit;

    // blit && ewit ==> regular clause entry
    // !blit && ewit ==> witness cube reference
    if (!blit) { // cube stack reference.
      extend_cube_stack (idx, stats);
      continue;
    }
    assert (ewit);
    if (ival (blit) == blit || ival (ewit) == ewit) {
      stats.extend_blocked++;
      continue;
    }

    // start by decoding the first size field
    const int size_field = clause_data[idx];
    bool wit_embedded, id_long;
    unsigned other_lits_size;
    decode_size_field (size_field, wit_embedded, id_long, other_lits_size);
    size_t idl_pos = idx + (id_long ? 2 : 1);
    size_t cur_literal = idl_pos + other_lits_size;

    bool satisfied = false;
    int new_blit = 0;
    while (cur_literal != idl_pos) {
      const int elit = clause_data[cur_literal];
      if (!satisfied && ival (elit) == elit) {
        new_blit = elit;
        clause_data[cur_literal] = blit;
        satisfied = true;
      }
      cur_literal--;
    }

    if (!satisfied) {
      assert (ival (ewit) != ewit);
      const size_t var = abs (ewit);
      if (var >= vals.size ())
        vals.resize (var + 1, false);
      vals[var] = !vals[var];
      internal->stats.extended++;
#ifndef QUIET
      stats.flipped++;
#endif
    }
    if (new_blit) {
      LOG ("updating blit from %d to %d", blit, new_blit);
      p->blit = new_blit;
    }
    stats.clauses_read++;
  }

  internal->stats.extend_clause_blocked += stats.extend_blocked;
  internal->stats.extend_clause_read += stats.clauses_read;
  PHASE ("extend", internal->stats.extensions,
         "extended through extension stack of size %" PRId64,
         stats.extension_size);
  PHASE ("extend", internal->stats.extensions,
         "flipped %" PRId64 " literals during extension", stats.flipped);
  extended = true;
  LOG ("extended");
}

/* --------------------------------------------------------------------------
 */
bool External::traverse_cube_stack (WitnessIterator &it, uint32_t ss_idx) {
  vector<int> witness;
  auto q = clause_data.begin () + ss_idx;

  // read the witness cube and store it into witness
  while (*q) {
    const int ewit = *q++;
    witness.push_back (ewit);
  }

  q++; // Skip the cube terminating '0'.

  vector<int> clause;

  while (*q) {
    bool wit_embedded, id_long;
    unsigned other_lits_size;
    decode_size_field (*q, wit_embedded, id_long, other_lits_size);

    assert (!wit_embedded);
    assert (other_lits_size);

    int64_t id = decode_id (q, id_long);

    assert (id);

    q += (id_long ? 3 : 2); // q points to the first literal of the clause.

    auto end_of_lits = q + other_lits_size;

    clause.clear ();
    while (q != end_of_lits) {
      clause.push_back (*q++);
    }

    if (!it.witness (clause, witness, id)) {
      return false;
    }
  }
  return true;
}

bool External::traverse_witnesses_backward (WitnessIterator &it) {
  if (internal->unsat)
    return true;

  vector<int> clause, witness;

  auto p = witness_data.end ();

  while (p != witness_data.begin ()) {
    const WitnessEntry &entry = *--p;
    const uint64_t idx = entry.idx;
    const int blit = entry.blit;
    const int ewit = entry.ewit;

    if (!blit) {
      traverse_cube_stack (it, idx);
      continue;
    }
    assert (ewit);

    auto q = clause_data.begin () + idx;

    bool wit_embedded, id_long;
    unsigned other_lits_size;
    decode_size_field (*q, wit_embedded, id_long, other_lits_size);

    int64_t id = decode_id (q, id_long);

    auto lit = q + (id_long ? 3 : 2);

    clause.clear ();
    clause.push_back (blit);

    auto end_of_lits = lit + other_lits_size;

    while (lit != end_of_lits)
      clause.push_back (*lit++);

    if (wit_embedded)
      clause.push_back (ewit);

    witness.clear ();
    witness.push_back (ewit);

    assert (id);

    if (!it.witness (clause, witness, id))
      return false;
  }
  return true;
}

bool External::traverse_witnesses_forward (WitnessIterator &it) {
  if (internal->unsat)
    return true;

  vector<int> clause, witness;

  auto p = witness_data.begin ();

  while (p != witness_data.end ()) {
    const WitnessEntry &entry = *p++;
    const uint64_t idx = entry.idx;
    const int blit = entry.blit;
    const int ewit = entry.ewit;

    if (!blit) {
      traverse_cube_stack (it, idx);
      continue;
    }

    assert (ewit);

    auto q = clause_data.begin () + idx;

    bool wit_embedded, id_long;
    unsigned other_lits_size;
    decode_size_field (*q, wit_embedded, id_long, other_lits_size);

    int64_t id = decode_id (q, id_long);

    auto lit = q + (id_long ? 3 : 2);
    auto end_of_lits = lit + other_lits_size;

    clause.clear ();
    clause.push_back (blit);

    if (wit_embedded)
      clause.push_back (ewit);

    while (lit != end_of_lits)
      clause.push_back (*lit++);

    witness.clear ();
    witness.push_back (ewit);

    assert (id);

    if (!it.witness (clause, witness, id))
      return false;
  }

  return true;
}
/*------------------------------------------------------------------------*/

void External::conclude_sat () {
  if (!internal->proof || concluded)
    return;
  concluded = true;
  if (!extended)
    extend ();
  vector<int> model;
  for (int idx = 1; idx <= max_var; idx++) {
    if (ervars[idx])
      continue;
    const int lit = ival (idx);
    model.push_back (lit);
  }
  internal->proof->conclude_sat (model);
}

} // namespace CaDiCaL
