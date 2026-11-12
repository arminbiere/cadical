#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/
// In incremental solving after a first call to 'solve' has finished and
// before calling the internal 'solve' again incrementally we have to
// restore clauses which have the negation of a literal as a witness literal
// in the extension data, which was added as original literal in a new
// clause or in an assumption.  This procedure has to be applied
// recursively, i.e., the literals of restored clauses are treated in the
// same way as literals of a new original clause.
//
// To figure out whether literals are such witnesses we have a 'witness'
// bit for each external literal, which is set when weakening a clause.
// The witness bits are recomputed while restoring clauses.

// We further mark in the external solver newly internalized external
// literals in 'add' and 'assume' since the last call to 'solve' as tainted
// if they occur negated as a witness literal in the extension data. Then
// we go through the extension data and restore all clauses which have a
// tainted literal (and its negation a marked as witness).
//
// Since the API contract disallows to call 'val' and 'failed' in an
// 'UNKNOWN' state. We do not have to internalize literals there.
//
// In order to have tainted literals accepted by the internal solver they
// have to be active and thus we might need to 'reactivate' them before
// restoring clauses if they are inactive. In case they have completely
// been eliminated and removed from the internal solver in 'compact', then
// we just use a new internal variable.  This is performed in 'internalize'
// during marking external literals as tainted.
//
// To check that this approach is correct the external solver can maintain a
// stack of original clauses and current assumptions both in terms of
// external literals.  Whenever 'solve' determines that the current
// incremental call is satisfiable we check that the (extended) witness does
// satisfy the saved original clauses, as well as all the assumptions. To
// enable these checks set 'opts.check' as well as 'opts.checkwitness' and
// 'opts.checkassumptions' all to 'true'.  The model based tester actually
// prefers to enable the 'opts.check' option and the other two are 'true' by
// default anyhow.
//
// See our SAT'19 paper [FazekasBiereScholl-SAT'19] for more details.
//
/*------------------------------------------------------------------------*/
static constexpr uint32_t CLAUSE_SMALL = 1u << 31;
static constexpr uint32_t EMBEDDED = 1u << 30;
static constexpr uint32_t ID_LONG = 1u << 29;
static constexpr uint32_t SIZE_MASK = (1u << 29) - 1;

static inline void decode_size_field (const int size_field,
                                      bool &wit_embedded, bool &id_long,
                                      unsigned &other_lits_size) {
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

/*------------------------------------------------------------------------*/
void External::restore_clause (vector<int>::const_iterator begin,
                               vector<int>::const_iterator end,
                               const int64_t id, const int ewit,
                               const int blit) {
  LOG (begin, end, "restoring external clause[%" PRId64 "]", id);

  assert (eclause.empty ());
  assert (id);

  auto restore_lit = [this] (int elit) {
    eclause.push_back (elit);

    if (internal->proof && internal->lrat) {
      unsigned eidx = (elit > 0) + 2u * (unsigned) abs (elit);
      assert ((size_t) eidx < ext_units.size ());
      const int64_t unit_id = ext_units[eidx];
      bool added = ext_flags[abs (elit)];
      if (unit_id && !added) {
        ext_flags[abs (elit)] = true;
        internal->lrat_chain.push_back (unit_id);
      }
    }

    const int ilit = internalize (elit);
    internal->add_original_lit (ilit);
    internal->stats.restored_literals++;
  };

  for (auto p = begin; p != end; p++) {
    restore_lit (*p);
  }
  if (blit) {
    LOG ("adding blocking literal (external %d) back to the clause", blit);
    restore_lit (blit);
  }
  if (ewit) {
    LOG ("adding witness (external %d) back to the clause", ewit);
    restore_lit (ewit);
  }
  if (internal->proof && internal->lrat) {
    for (const auto &elit : eclause) {
      ext_flags[abs (elit)] = false;
    }
  }
  internal->finish_added_clause_with_id (id, true);
  eclause.clear ();
  internal->stats.restored_clauses++;
}

bool External::restore_cube_stack (uint32_t idx,
                                   vector<bool> &skipped_witness,
                                   RestoreStats &clauses) {
  auto q = clause_data.begin () + idx;
  bool restore_clauses = false;

  while (*q) {
    const int ewit = *q++;
    if (marked (tainted, -ewit))
      restore_clauses = true;
  }
  while (*q) {
    q++;
  }
  q++; // Skip cube terminator
  if (!restore_clauses && !internal->opts.restoreall) {
    LOG ("untainted and not forced to restore all clauses.");
    // now also mark witnesses as skipped.
    q = clause_data.begin () + idx;
    while (*q) {
      const int ewit = *q++;
      if (!marked (skipped_witness, ewit))
        mark (skipped_witness, ewit);
    }
    return false;
  }

  while (*q != 0) {
    clauses.total++;
    bool wit_embedded, id_long;
    unsigned other_lits_size;
    decode_size_field (*q, wit_embedded, id_long, other_lits_size);
    assert (!wit_embedded);

    int64_t id = decode_id (q, id_long);
    LOG ("id computed: %" PRId64 "(%s)", id, id_long ? "long" : "short");

    auto begin = q + (id_long ? 3 : 2);
    auto end = begin + other_lits_size;
    clauses.restored++;
    restore_clause (begin, end, id, 0, 0);

    q += 1 + (id_long ? 2 : 1) + other_lits_size;
  }
  fragmented_clause_data += q - (clause_data.begin () + idx) + 1;
  return true;
}

void External::defragment_clause_data () {
  LOG ("defragmenting clause data of %zu elements", clause_data.size ());

  size_t write = 0;

  for (auto p = witness_data.begin (); p != witness_data.end (); ++p) {
    WitnessEntry &entry = *p;
    const int blit = entry.blit;
    const uint64_t idx = entry.idx;

    if (!blit) {
      assert (!entry.ewit); // ewit
      auto begin = clause_data.begin () + idx;
      auto end = begin;
      // Skip the witness cube and its terminating zero.
      while (*end)
        ++end;
      ++end;

      // Skip all clause records until the final terminating zero.
      while (*end) {
        bool wit_embedded, id_long;
        unsigned other_lits_size;
        decode_size_field (*end, wit_embedded, id_long, other_lits_size);
        assert (!wit_embedded);

        end += 1 + other_lits_size + (id_long ? 2 : 1);
      }
      ++end; // Include the final terminating zero.
      const size_t stack_size = end - begin;

      assert (idx + stack_size <= clause_data.size ());

      // Update the cube stack index.
      entry.idx = write;

      // Move the complete shared stack.
      if (write != idx) {
        std::memmove (clause_data.data () + write,
                      clause_data.data () + idx, stack_size * sizeof (int));
      }
      write += stack_size;
      continue;
    }
    assert (entry.ewit);

    bool wit_embedded, id_long;
    unsigned other_lits_size;
    decode_size_field (clause_data[idx], wit_embedded, id_long,
                       other_lits_size);

    const size_t record_size = 1 + other_lits_size + (id_long ? 2 : 1);

    assert (idx + record_size <= clause_data.size ());

    // Update the index in the witness entry
    entry.idx = write;

    // Move the record to its compacted position.
    if (write != idx) {
      std::memmove (clause_data.data () + write, clause_data.data () + idx,
                    record_size * sizeof (int));
    }
    write += record_size;
  }

  clause_data.resize (write);
  shrink_vector (clause_data);
  fragmented_clause_data = 0;

  LOG ("defragmented clause data to %zu elements", clause_data.size ());
}

void External::restore () {

  assert (internal->opts.restoreall || !tainted.empty ());

  PROFILE_SCOPE (restore);
  internal->stats.restorations++;

  RestoreStats clauses = {};

  if (internal->opts.restoreall && tainted.empty ())
    PHASE ("restore", internal->stats.restorations,
           "forced to restore all clauses");

#ifndef QUIET
  {
    unsigned numtainted = 0;
    for (const auto b : tainted)
      if (b)
        numtainted++;

    PHASE ("restore", internal->stats.restorations,
           "starting with %u tainted literals %.0f%%", numtainted,
           percent (numtainted, 2u * max_var));
  }
#endif

  vector<bool> skipped_witness; // For recomputing the witness bits.

  auto read = witness_data.begin ();
  auto write = witness_data.begin ();
  auto end = witness_data.end ();

  while (read != end) {
    const WitnessEntry &entry = *read++;
    const int ewit = entry.ewit;
    const int blit = entry.blit;
    const uint64_t idx = entry.idx;

    if (!blit) {
      assert (!ewit);
      if (!restore_cube_stack (idx, skipped_witness, clauses)) {
        *write++ = entry;
      }
      continue;
    }

    assert (ewit);
    clauses.total++;

    // restore the corresponding clause
    if (internal->opts.restoreall || marked (tainted, -ewit)) {

      bool wit_embedded, id_long;
      unsigned other_lits_size;

      // Now restore the next clause
      auto p = clause_data.begin () + idx;
      decode_size_field (*p, wit_embedded, id_long, other_lits_size);
      assert (wit_embedded); // should always hold here.

      int64_t id = decode_id (p, id_long);
      LOG ("id computed: %" PRId64 "(%s)", id, id_long ? "long" : "short");

      auto begin = p + (id_long ? 3 : 2);
      auto end_of_lits = begin + other_lits_size;

      clauses.restored++;
      restore_clause (begin, end_of_lits, id, ewit, blit);
      fragmented_clause_data += 1 + other_lits_size + (id_long ? 2 : 1);

      continue;
    }

    mark (skipped_witness, ewit);
    *write++ = entry;
  }

  witness_data.resize (write - witness_data.begin ());
  shrink_vector (witness_data);

  witness = std::move (skipped_witness);

  if (internal->opts.restoreall) {
    assert (witness_data.empty ());
    clause_data.clear ();
    shrink_vector (clause_data);
    fragmented_clause_data = 0;
  } else if (100 * fragmented_clause_data >
             internal->opts.restoredefraglim * clause_data.size ()) {
    internal->stats.restore_defrags++;
    defragment_clause_data ();
  }

#ifndef QUIET
  if (clauses.restored)
    PHASE ("restore", internal->stats.restorations,
           "restored %" PRId64 " clauses %.0f%% out of %" PRId64 " clauses",
           clauses.restored, percent (clauses.restored, clauses.total),
           clauses.total);
  else
    PHASE ("restore", internal->stats.restorations,
           "no clause restored out of %" PRId64 " clauses", clauses.total);
  {
    unsigned numtainted = 0;
    for (const auto &b : tainted)
      if (b)
        numtainted++;

    PHASE ("restore", internal->stats.restorations,
           "finishing with %u tainted literals %.0f%%", numtainted,
           percent (numtainted, 2u * max_var));
  }
#endif

  tainted.clear ();
  tainted.shrink_to_fit ();
}

} // namespace CaDiCaL
