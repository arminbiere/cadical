#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Signed marking or unmarking of a clause or the global 'clause'.

void Internal::mark (Clause *c) {
  for (const auto &lit : *c)
    mark (lit);
}

void Internal::mark2 (Clause *c) {
  for (const auto &lit : *c)
    mark2 (lit);
}

void Internal::unmark (Clause *c) {
  for (const auto &lit : *c)
    unmark (lit);
}

void Internal::mark_clause () {
  for (const auto &lit : clause)
    mark (lit);
}

void Internal::unmark_clause () {
  for (const auto &lit : clause)
    unmark (lit);
}

/*------------------------------------------------------------------------*/

// Mark the variables of an irredundant clause to 'have been removed', which
// will trigger these variables to be considered again in the next bounded
// variable elimination phase.  This is called from 'mark_garbage' below.
// Note that 'mark_removed (int lit)' will also mark the blocking flag of
// '-lit' to trigger reconsidering blocking clauses on '-lit'.

void Internal::mark_removed (Clause *c, int except) {
  LOG (c, "marking removed");
  assert (!c->main.redundant);
  for (const auto &lit : *c)
    if (lit != except)
      mark_removed (lit);
}

// Mark the variables of a (redundant or irredundant) clause to 'have been
// added', which triggers clauses with such a variables, to be considered
// both as a subsumed or subsuming clause in the next subsumption phase.
// This function is called from 'new_clause' below as well as in situations
// where a clause is shrunken (and thus needs to be at least considered
// again to subsume a larger clause).  We also use this to tell
// 'ternary' preprocessing reconsider clauses on an added literal as well as
// trying to block clauses on it.

inline void Internal::mark_added (int lit, int size, bool redundant) {
  mark_subsume (lit);
  if (size == 3)
    mark_ternary (lit);
  if (!redundant)
    mark_block (lit);
  if (size <= opts.factorsize && (opts.factorredundant > 1 || !redundant ||
                                  (opts.factorredundant == 1 && size == 2)))
    mark_factor (lit);
}

void Internal::mark_added (Clause *c) {
  LOG (c, "marking added");
  assert (likely_to_be_kept_clause (c));
  for (const auto &lit : *c)
    mark_added (lit, c->size (), c->main.redundant);
}

/*------------------------------------------------------------------------*/

Clause *Internal::new_clause (bool red, int glue) {

  assert (clause.size () <= (size_t) INT_MAX);
  const int size = (int) clause.size ();
  assert (size >= 2);

  if (glue > size)
    glue = size;

  const bool with_id = allocate_lrat_id ();
  size_t bytes = Clause::bytes_to_allocate (size, with_id);
  char* raw_clause = new char[bytes];
  if (!with_id)
    raw_clause -= Clause::offset (size == 2);
  Clause *c = (Clause*) raw_clause;
  DeferDeleteArray<char> clause_delete (raw_clause);

#ifndef NDEBUG
    c->main.has_id = with_id;
#endif
  if (with_id)
    c->id () = ++clause_id;

  c->main.conditioned = false;
  c->main.covered = false;
  c->main.enqueued = false;
  c->main.frozen = false;
  c->main.garbage = false;
  c->main.gate = false;
  c->main.hyper = false;
  c->main.instantiated = false;
  c->main.moved = false;
  c->main.reason = false;
  c->main.redundant = red;
  c->main.transred = false;
  c->main.subsume = false;
  c->main.swept = false;
  c->main.flushed = false;
  c->main.vivified = false;
  c->main.vivify = false;
  c->main.used = 0;

  c->main.size = size;
  c->main.allocated_as_binary = (size == 2);

  if (with_id || c->size () != 2) {
    c->glue () = glue;
    c->pos () = 2;
  }

  for (int i = 0; i < size; i++)
    c->literals[i] = clause[i];

  // Just checking that we did not mess up our sophisticated memory layout.
  // This might be compiler dependent though. Crucial for correctness.
  //
  assert (c->allocated_bytes (with_id) == bytes);

  stats.clauses_now_total++;
  stats.clauses++;

  if (red) {
    stats.clauses_now_red++;
    stats.clauses_redundant++;
  } else {
    stats.irredundant_literals += size;
    stats.clauses_now_irr++;
    stats.clauses_irredundant++;
  }
  if (size == 2)
    new_binary_since_dedup = true;

  clauses.push_back (c);
  clause_delete.release ();
#ifdef LOGGING
  if (opts.logpointer)
    LOG (c, "new pointer %p", (void *) c);
  else
    LOG (c, "new");
#endif

  if (likely_to_be_kept_clause (c))
    mark_added (c);

  // assertions
  assert (c->main.moved == c->moved_clause.moved2);
  assert (c->main.garbage == c->moved_clause.garbage2);
  assert (c->main.reason == c->moved_clause.reason2);
  assert (c->main.redundant == c->moved_clause.redundant2);
  return c;
}

/*------------------------------------------------------------------------*/

void Internal::promote_clause (Clause *c, int new_glue) {
  assert (c->main.redundant);
  assert (new_glue);
  const int tier1limit = tier1[false];
  const int tier2limit = max (tier1limit, tier2[false]);
  if (!c->main.redundant)
    return;
  if (c->main.hyper)
    return;
  if (c->size () == 2) {
    return;
  }
  assert (c->size () != 2);
  int old_glue = c->glue ();
  if (new_glue >= old_glue)
    return;
  c->main.used = max_used;
  if (old_glue > tier1limit && new_glue <= tier1limit) {
    LOG (c, "promoting with new glue %d to tier1", new_glue);
    stats.clause_promoted_tier1++;
  } else if (old_glue > tier2limit && new_glue <= tier2limit) {
    LOG (c, "promoting with new glue %d to tier2", new_glue);
    stats.clause_promoted_tier2++;
  } else if (old_glue <= tier2limit)
    LOG (c, "keeping with new glue %d in tier2", new_glue);
  else
    LOG (c, "keeping with new glue %d in tier3", new_glue);
  stats.clause_improved_glue++;
  c->glue () = new_glue;
}
/*------------------------------------------------------------------------*/

void Internal::promote_clause_glue_only (Clause *c, int new_glue) {
  assert (c->main.redundant);
  assert (new_glue);
  if (c->main.hyper)
    return;
  assert (c->size () != 2);
  int old_glue = c->glue ();
  const int tier1limit = tier1[false];
  const int tier2limit = max (tier1limit, tier2[false]);
  if (new_glue >= old_glue)
    return;
  if (new_glue <= tier1limit) {
    LOG (c, "promoting with new glue %d to tier1", new_glue);
    stats.clause_promoted_tier1++;
  } else if (old_glue > tier2limit && new_glue <= tier2limit) {
    LOG (c, "promoting with new glue %d to tier2", new_glue);
    stats.clause_promoted_tier2++;
  } else if (old_glue <= tier2limit)
    LOG (c, "keeping with new glue %d in tier2", new_glue);
  else
    LOG (c, "keeping with new glue %d in tier3", new_glue);
  stats.clause_improved_glue++;
  c->glue () = new_glue;
}

/*------------------------------------------------------------------------*/

// Shrinking a clause, e.g., removing one or more literals, requires to fix
// the 'pos' field, if it exists and points after the new last literal. We
// also have adjust the global statistics counter of irredundant literals
// for irredundant clauses, and also adjust the glue value of redundant
// clauses if the size becomes smaller than the glue.  Also mark the
// literals in the resulting clause as 'added'.  The result is the number of
// (aligned) removed bytes, resulting from shrinking the clause.
//
size_t Internal::shrink_clause (Clause *c, int new_size) {
  if (opts.check && opts.checkproof >= 2 && is_external_forgettable (c->id ()))
    mark_garbage_external_forgettable (c->id ());
  assert (new_size >= 2);
  int old_size = c->size ();
  assert (new_size < old_size);
#ifndef NDEBUG
  for (int i = c->size (); i < new_size; i++)
    c->literals[i] = 0;
#endif

  if (c->pos () >= new_size)
    c->pos () = 2;

  size_t old_bytes = c->raw_bytes ();
  c->main.size = new_size;
  size_t new_bytes = c->raw_bytes ();
  size_t res = old_bytes - new_bytes;

  if (c->main.redundant) {
    if (c->size () != 2)
      promote_clause_glue_only (c, min (c->size () - 1, c->glue ()));
  }
  else {
    int delta_size = old_size - new_size;
    assert (stats.irredundant_literals >= delta_size);
    stats.irredundant_literals -= delta_size;
  }

  if (likely_to_be_kept_clause (c))
    mark_added (c);

  return res;
}

// Makes a redundant clause irredundant and update the statistics
void Internal::make_irredundant (Clause *subsuming) {
  assert (subsuming->main.redundant);
  assert (!subsuming->main.garbage);
  LOG ("turning redundant subsuming clause into irredundant clause");
  subsuming->main.redundant = false;
  if (proof)
    proof->strengthen (allocate_lrat_id() ? subsuming->id () : 0);
  stats.clauses_now_irr++;
  stats.clauses_irredundant++;
  stats.irredundant_literals += subsuming->size ();
  assert (stats.clauses_now_red > 0);
  stats.clauses_now_red--;
  assert (stats.clauses_redundant > 0);
  stats.clauses_redundant--;
  // ... and keep 'stats.clauses'.
}

// This is the 'raw' deallocation of a clause.  If the clause is in the
// arena nothing happens.  If the clause is not in the arena its memory is
// reclaimed immediately.

void Internal::deallocate_clause (Clause *c) {
  char *p = (char *) c;
  const bool with_lrat = allocate_lrat_id();
  if (!with_lrat)
    p += Clause::offset (c->allocated_as_binary ());
  if (arena.contains (c))
    return;
  LOG (c, "deallocate pointer %p, %s ID", (void *) c, with_lrat ? "with" : "without");
  delete[] p;
}

void Internal::delete_clause (Clause *c) {
  LOG (c, "delete pointer %p with %zd", (void *) c, stats.garbage_bytes);
  int size = c->main.moved ? c->copy ()->size () : c->size ();
  bool garbage = c->main.moved ? false : c->main.garbage;
  size_t bytes = c->raw_bytes (size);
  stats.collected += bytes;
  if (garbage) {
    assert (stats.garbage_bytes >= (int64_t) bytes);
    stats.garbage_bytes -= bytes;
    assert (stats.garbage_clauses > 0);
    stats.garbage_clauses--;
    assert (stats.garbage_literals >= size);
    stats.garbage_literals -= size;

    // See the discussion in 'propagate' on avoiding to eagerly trace binary
    // clauses as deleted (produce 'd ...' lines) as soon they are marked
    // garbage.  We avoid this and only trace them as deleted when they are
    // actually deleted here.  This allows the solver to propagate binary
    // garbage clauses without producing incorrect 'd' lines.  The effect
    // from the proof perspective is that the deletion of these binary
    // clauses occurs later in the proof file.
    //
    if (proof && size == 2 && !c->main.flushed) {
      proof->delete_clause (c);
    }
  }
  deallocate_clause (c);
}

// We want to eagerly update statistics as soon clauses are marked garbage.
// Otherwise 'report' for instance gives wrong numbers after 'subsume'
// before the next 'reduce'.  Thus we factored out marking and accounting
// for garbage clauses.
//
// Eagerly deleting clauses instead is problematic, since references to
// these clauses need to be flushed, which is too costly to do eagerly.
//
// We also update garbage statistics at this point.  This helps to
// determine whether the garbage collector should be called during for
// instance bounded variable elimination, which usually generates lots of
// garbage clauses.
//
// In order not to miss any update to these clause statistics we call
// 'check_clause_stats' after garbage collection in debugging mode.
//
void Internal::mark_garbage (Clause *c) {

  assert (!c->main.garbage);

  // Delay tracing deletion of binary clauses.  See the discussion above in
  // 'delete_clause' and also in 'propagate'.
  //
  if (proof && (c->size () != 2 || !watching ())) {
    c->main.flushed = true;
    proof->delete_clause (c);
  }

  // Because of the internal model checking, external forgettable clauses
  // must be marked as removed already upon mark_garbage, can not wait until
  // actual deletion.
  if (opts.check && opts.checkproof >= 2 && is_external_forgettable (c->id ()))
    mark_garbage_external_forgettable (c->id ());

  assert (stats.clauses_now_total > 0);
  stats.clauses_now_total--;

  size_t bytes = c->raw_bytes ();
  if (c->main.redundant) {
    assert (stats.clauses_now_red > 0);
    stats.clauses_now_red--;
  } else {
    assert (stats.clauses_now_irr > 0);
    stats.clauses_now_irr--;
    assert (stats.irredundant_literals >= c->size ());
    stats.irredundant_literals -= c->size ();
    mark_removed (c);
  }
  stats.garbage_bytes += bytes;
  stats.garbage_clauses++;
  stats.garbage_literals += c->size ();
  c->main.garbage = true;
  c->main.used = 0;

  LOG (c, "marked garbage pointer %p with %zd", (void *) c, stats.garbage_bytes);
}

/*------------------------------------------------------------------------*/

// Almost the same function as 'search_assign' except that we do not pretend
// to learn a new unit clause (which was confusing in log files).

void Internal::assign_original_unit (int64_t id, int lit) {
  assert (!unsat);
  const int idx = vidx (lit);
  assert (!vals[idx]);
  assert (!flags (idx).eliminated ());
  Var &v = var (idx);
  v.level = 0;
  v.trail = get_trail_size ();
  v.reason = 0;
  const signed char tmp = sign (lit);
  set_val (idx, tmp);
  trail.push_back (lit);
  num_assigned++;
  const unsigned uidx = vlit (lit);
  if (lrat || frat)
    unit_clauses (uidx) = id;
  LOG ("original unit assign %d", lit);
  assert (num_assigned == trail.size () || level);
  mark_fixed (lit);
  if (level)
    return;
}

// New clause added through the API, e.g., while parsing a DIMACS file.
// Also used by external_propagate in various different modes.
// clause, original, lrat_chain and external->eclause are set.
// from_propagator and force_no_backtrack change the behaviour.
// sometimes the pointer to the new clause is needed, therefore it is
// made sure that newest_clause points to the new clause upon return.

void Internal::add_new_original_clause (int64_t id) {

  if (!from_propagator && level && !opts.ilb) {
    backtrack_without_updating_phases ();
  } else if (earliest_changed_val) {
    assert (val (earliest_changed_val));
    int new_level = var (earliest_changed_val).level - 1;
    assert (new_level >= 0);
    backtrack_without_updating_phases (new_level);
  }
  assert (!earliest_changed_val);
  LOG (original, "original clause");
  assert (clause.empty ());
  bool skip = false;
  unordered_set<int> learned_levels;
  size_t unassigned = 0;
  newest_clause = 0;
  if (unsat) {
    LOG ("skipping clause since formula is already inconsistent");
    skip = true;
  } else {
    assert (clause.empty ());
    for (const auto &lit : original) {
      int tmp = marked (lit);
      if (tmp > 0) {
        LOG ("removing duplicated literal %d", lit);
      } else if (tmp < 0) {
        LOG ("tautological since both %d and %d occur", -lit, lit);
        skip = true;
      } else {
        mark (lit);
        tmp = fixed (lit);
        if (tmp < 0) {
          LOG ("removing falsified literal %d", lit);
          if (lrat) {
            int elit = externalize (lit);
            unsigned eidx = (elit > 0) + 2u * (unsigned) abs (elit);
            // the external units are handled somewhere else
            if (!external->ext_units[eidx]) {
              int64_t uid = unit_id (-lit);
              lrat_chain.push_back (uid);
            }
          }
        } else if (tmp > 0) {
          LOG ("satisfied since literal %d true", lit);
          skip = true;
        } else {
          clause.push_back (lit);
          assert (flags (lit).status != Flags::UNUSED);
          tmp = val (lit);
          if (tmp)
            learned_levels.insert (var (lit).level);
          else
            unassigned++;
        }
      }
    }
    for (const auto &lit : original)
      unmark (lit);
  }
  if (skip) {
    if (from_propagator) {
      stats.up_learn_satisfied++;

      // In case it was a skipped external forgettable, we need to mark it
      // immediately as removed

      if (opts.check && opts.checkproof >= 2 && is_external_forgettable (id))
        mark_garbage_external_forgettable (id);
    }
    if (proof) {
      proof->delete_external_original_clause (id, false, external->eclause);
    }
  } else {
    int64_t new_id = id;
    const size_t size = clause.size ();
    if (original.size () > size) {
      new_id = ++clause_id;
      if (proof) {
        if (lrat)
          lrat_chain.push_back (id);
        proof->add_derived_clause (new_id, false, clause, lrat_chain);
        proof->delete_external_original_clause (id, false,
                                                external->eclause);
      }
      external->check_learned_clause ();

      if (from_propagator) {
        // The original form of the added clause is immediately forgotten
        // TODO: shall we save and check the simplified form? (one with
        // new_id)
        if (opts.check && opts.checkproof >= 2 && is_external_forgettable (id))
          mark_garbage_external_forgettable (id);
      }
    }
    external->eclause.clear ();
    lrat_chain.clear ();
    if (!size) {
      if (from_propagator)
        stats.up_learn_empty++;
      assert (!unsat);
      if (!original.size ())
        VERBOSE (1, "found empty original clause");
      else
        VERBOSE (1, "found falsified original clause");
      unsat = true;
      conflict_id = new_id;
      marked_failed = true;
      conclusion.push_back (new_id);
    } else if (size == 1) {
      handle_external_clause (0, new_id);
    } else {
      move_literals_to_watch ();
#ifndef NDEBUG
      check_watched_literal_invariants ();
#endif
      int glue = (int) (learned_levels.size () + unassigned);
      assert (glue <= (int) clause.size ());
      bool clause_redundancy = from_propagator && ext_clause_forgettable;
      Clause *c = new_clause (clause_redundancy, glue);
      if (allocate_lrat_id())
        c->id () = new_id;
      clause_id--;
      original.clear ();
      handle_external_clause (c); // handle_external_clause uses clause
      watch_clause (c);           // and may change the watched literal
      clause.clear ();            // therefore it is cleared afterwards
      newest_clause = c;
    }
  }
  clause.clear ();
  lrat_chain.clear ();
}

// Add learned new clause during conflict analysis and watch it. Requires
// that the clause is at least of size 2, and the first two literals
// are assigned at the highest decision level.
//
Clause *Internal::new_learned_redundant_clause (int glue) {
  assert (clause.size () > 1);
#ifndef NDEBUG
  for (size_t i = 2; i < clause.size (); i++)
    assert (var (clause[0]).level >= var (clause[i]).level),
        assert (var (clause[1]).level >= var (clause[i]).level);
#endif
  external->check_learned_clause ();
  if (proof) {
    proof->add_derived_clause (clause_id + 1, true, clause, lrat_chain);
  }
  Clause *res = new_clause (true, glue);
  assert (watching ());
  watch_clause (res);
  return res;
}

// Add hyper binary resolved clause during 'probing'.
//
Clause *Internal::new_hyper_binary_resolved_clause (bool red, int glue) {
  external->check_learned_clause ();
  if (proof) {
    proof->add_derived_clause (clause_id + 1, red, clause, lrat_chain);
  }
  Clause *res = new_clause (red, glue);
  assert (watching ());
  watch_clause (res);
  return res;
}

// Add hyper ternary resolved clause during 'ternary'.
//
Clause *Internal::new_hyper_ternary_resolved_clause (bool red) {
  external->check_learned_clause ();
  if (proof) {
    proof->add_derived_clause (clause_id + 1, red, clause, lrat_chain);
  }
  size_t size = clause.size ();
  Clause *res = new_clause (red, size);
  assert (!watching ());
  return res;
}

Clause *Internal::new_factor_clause (int witness) {
  external->check_learned_clause ();
  stats.factor_added_clauses++;
  stats.factor_added_literals += clause.size ();
  if (proof) {
    if (witness)
      proof->add_derived_rat_clause (
          clause_id + 1, false, externalize (witness), clause, lrat_chain);
    else
      proof->add_derived_clause (clause_id + 1, false, clause, lrat_chain);
  }
  Clause *res = new_clause (false, 0);
  assert (!watching ());
  assert (occurring ());
  for (const auto &lit : *res) {
    occs (lit).push_back (res);
  }
  return res;
}

// Add hyper ternary resolved clause during 'congruence' and watch it
//
Clause *
Internal::new_hyper_ternary_resolved_clause_and_watch (bool red,
                                                       bool full_watching) {
  external->check_learned_clause ();
  if (proof) {
    proof->add_derived_clause (clause_id + 1, red, clause, lrat_chain);
  }
  size_t size = clause.size ();
  Clause *res = new_clause (red, size);
  if (full_watching) {
    assert (watching ());
    watch_clause (res);
  }
  return res;
}

// Add a new clause with same glue and redundancy as 'orig' but literals are
// assumed to be in 'clause' in 'decompose' and 'vivify'.
//
Clause *Internal::new_clause_as (const Clause *orig) {
  external->check_learned_clause ();
  if (proof) {
    proof->add_derived_clause (clause_id + 1, orig->main.redundant, clause,
                               lrat_chain);
  }
  const int new_glue = orig->size () == 2 ? 1 : orig->glue ();
  Clause *res = new_clause (orig->main.redundant, new_glue);
  assert (watching ());
  watch_clause (res);
  return res;
}

// Add resolved clause during resolution, e.g., bounded variable
// elimination, but do not connect its occurrences here.
//
Clause *Internal::new_resolved_irredundant_clause () {
  external->check_learned_clause ();
  if (proof) {
    proof->add_derived_clause (clause_id + 1, false, clause, lrat_chain);
  }
  Clause *res = new_clause (false);
  assert (!watching ());
  return res;
}

void Internal::decay_clauses_upon_incremental_clauses () {
  if (!opts.incdecay)
    return;
  if (!stats.searches)
    return;
  if (stats.conflicts < lim.incremental_decay)
    return;

  PHASE ("decay", stats.incremental_decay,
         "decaying clauses with next decaying at conflict %" PRId64
         "(after the next incremental call)",
         lim.incremental_decay);

  for (auto c : clauses) {
    if (c->main.garbage)
      continue;
    if (!c->main.redundant)
      continue;
    if (c->size () == 2)
      continue;
    switch (opts.incdecay) {
    case 1: // my intuition
      ++c->glue ();
      break;
    case 2: // Armin's idea
      if (c->glue () < tier1[false])
        c->main.used = 1;
      break;
    case 3:
      if (c->glue () < tier1[false])
        c->main.used = 1;
      ++c->glue ();
      break;
    default:
      break;
    }
  }

  lim.incremental_decay += stats.conflicts + opts.incdecayint;
  ++stats.incremental_decay;
  last.incremental_decay.last_id = clause_id;
}
} // namespace CaDiCaL
