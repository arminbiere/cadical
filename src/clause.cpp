#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Signed marking or unmarking of a clause or the global 'clause'.

void Internal::mark (Clause * c) {
  for (const auto & lit : *c) mark (lit);
}

void Internal::mark2 (Clause * c) {
  for (const auto & lit : *c) mark2 (lit);
}

void Internal::unmark (Clause * c) {
  for (const auto & lit : *c) unmark (lit);
}

void Internal::mark_clause () {
  for (const auto & lit : clause) mark (lit);
}

void Internal::unmark_clause () {
  for (const auto & lit : clause) unmark (lit);
}

/*------------------------------------------------------------------------*/

// Mark the variables of an irredundant clause to 'have been removed', which
// will trigger these variables to be considered again in the next bounded
// variable elimination phase.  This is called from 'mark_garbage' below.
// Note that 'mark_removed (int lit)' will also mark the blocking flag of
// '-lit' to trigger reconsidering blocking clauses on '-lit'.

void Internal::mark_removed (Clause * c, int except) {
  LOG (c, "marking removed");
  assert (!c->redundant);
  for (const auto & lit : *c)
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
}

void Internal::mark_added (Clause * c) {
  LOG (c, "marking added");
  assert (likely_to_be_kept_clause (c));
  for (const auto & lit : *c)
    mark_added (lit, c->size, c->redundant);
}

/*------------------------------------------------------------------------*/

Clause * Internal::new_clause (bool red, int glue) {

  assert (clause.size () <= (size_t) INT_MAX);
  const int size = (int) clause.size ();
  assert (size >= 2);

  if (glue > size) glue = size;

  // Determine whether this clauses should be kept all the time.
  //
  bool keep;
  if (!red) keep = true;
  else if (glue <= opts.reducetier1glue) keep = true;
  else keep = false;

  size_t bytes = Clause::bytes (size);
  Clause * c = (Clause *) new char[bytes];

  stats.added.total++;
#ifdef LOGGING
  c->id = stats.added.total;
#endif

  c->conditioned = false;
  c->covered = false;
  c->enqueued = false;
  c->frozen = false;
  c->garbage = false;
  c->gate = false;
  c->hyper = false;
  c->instantiated = false;
  c->keep = keep;
  c->moved = false;
  c->reason = false;
  c->redundant = red;
  c->transred = false;
  c->subsume = false;
  c->vivified = false;
  c->vivify = false;
  c->used = 0;

  c->glue = glue;
  c->size = size;
  c->pos = 2;

  for (int i = 0; i < size; i++) c->literals[i] = clause[i];

  // Just checking that we did not mess up our sophisticated memory layout.
  // This might be compiler dependent though. Crucial for correctness.
  //
  assert (c->bytes () == bytes);

  stats.current.total++;
  stats.added.total++;

  if (red) {
    stats.current.redundant++;
    stats.added.redundant++;
  } else {
    stats.irrbytes += bytes;
    stats.current.irredundant++;
    stats.added.irredundant++;
  }

  clauses.push_back (c);
  LOG (c, "new pointer %p", (void*) c);

  if (likely_to_be_kept_clause (c)) mark_added (c);

  return c;
}

/*------------------------------------------------------------------------*/

void Internal::promote_clause (Clause * c, int new_glue) {
  assert (c->redundant);
  if (c->keep) return;
  if (c->hyper) return;
  int old_glue = c->glue;
  if (new_glue >= old_glue) return;
  if (!c->keep && new_glue <= opts.reducetier1glue) {
    LOG (c, "promoting with new glue %d to tier1", new_glue);
    stats.promoted1++;
    c->keep = true;
  } else if (old_glue > opts.reducetier2glue &&
             new_glue <= opts.reducetier2glue) {
    LOG (c, "promoting with new glue %d to tier2", new_glue);
    stats.promoted2++;
    c->used = 2;
  } else if (c->keep)
    LOG (c, "keeping with new glue %d in tier1", new_glue);
  else if (old_glue <= opts.reducetier2glue)
    LOG (c, "keeping with new glue %d in tier2", new_glue);
  else
    LOG (c, "keeping with new glue %d in tier3", new_glue);
  stats.improvedglue++;
  c->glue = new_glue;
}

/*------------------------------------------------------------------------*/

// Shrinking a clause, e.g., removing one or more literals, requires to fix
// the 'pos' field, if it exists and points after the new last literal, has
// to adjust the global statistics counter of allocated bytes for
// irredundant clauses, and also adjust the glue value of redundant clauses
// if the size becomes smaller than the glue.  Also mark the literals in the
// resulting clause as 'added'.  The result is the number of (aligned)
// removed bytes, resulting from shrinking the clause.
//
size_t Internal::shrink_clause (Clause * c, int new_size) {

  assert (new_size >= 2);
  assert (new_size < c->size);
#ifndef NDEBUG
  for (int i = c->size; i < new_size; i++)
    c->literals[i] = 0;
#endif

  if (c->pos >= new_size) c->pos = 2;

  size_t old_bytes = c->bytes ();
  c->size = new_size;
  size_t new_bytes = c->bytes ();
  size_t res = old_bytes - new_bytes;

  if (c->redundant) promote_clause (c, min (c->size-1, c->glue));
  else if (old_bytes > new_bytes) {
    assert (stats.irrbytes >= (int64_t) res);
    stats.irrbytes -= res;
  }

  if (likely_to_be_kept_clause (c)) mark_added (c);

  return res;
}

// This is the 'raw' deallocation of a clause.  If the clause is in the
// arena nothing happens.  If the clause is not in the arena its memory is
// reclaimed immediately.

void Internal::deallocate_clause (Clause * c) {
  char * p = (char*) c;
  if (arena.contains (p)) return;
  LOG (c, "deallocate pointer %p", (void*) c);
  delete [] p;
}

void Internal::delete_clause (Clause * c) {
  LOG (c, "delete pointer %p", (void*) c);
  size_t bytes = c->bytes ();
  stats.collected += bytes;
  if (c->garbage) {
    assert (stats.garbage >= (int64_t) bytes);
    stats.garbage -= bytes;

    // See the discussion in 'propagate' on avoiding to eagerly trace binary
    // clauses as deleted (produce 'd ...' lines) as soon they are marked
    // garbage.  We avoid this and only trace them as deleted when they are
    // actually deleted here.  This allows the solver to propagate binary
    // garbage clauses without producing incorrect 'd' lines.  The effect
    // from the proof perspective is that the deletion of these binary
    // clauses occurs later in the proof file.
    //
    if (proof && c->size == 2)
      proof->delete_clause (c);
  }
  deallocate_clause (c);
}

// We want to eagerly update statistics as soon clauses are marked garbage.
// Otherwise 'report' for instance gives wrong numbers after 'subsume'
// before the next 'reduce'.  Thus we factored out marking and accounting
// for garbage clauses.
//
// Eagerly deleting clauses instead is problematic, since references to these
// clauses need to be flushed, which is too costly to do eagerly.
//
// We also update garbage statistics at this point.  This helps to
// determine whether the garbage collector should be called during for
// instance bounded variable elimination, which usually generates lots of
// garbage clauses.
//
// In order not to miss any update to these clause statistics we call
// 'check_clause_stats' after garbage collection in debugging mode.
//
void Internal::mark_garbage (Clause * c) {

  assert (!c->garbage);

  // Delay tracing deletion of binary clauses.  See the discussion above in
  // 'delete_clause' and also in 'propagate'.
  //
  if (proof && c->size != 2)
    proof->delete_clause (c);

  assert (stats.current.total > 0);
  stats.current.total--;

  size_t bytes = c->bytes ();
  if (c->redundant) {
    assert (stats.current.redundant > 0);
    stats.current.redundant--;
  } else {
    assert (stats.current.irredundant > 0);
    stats.current.irredundant--;
    assert (stats.irrbytes >= (int64_t) bytes);
    stats.irrbytes -= bytes;
    mark_removed (c);
  }
  stats.garbage += bytes;
  c->garbage = true;
  c->used = 0;

  LOG (c, "marked garbage pointer %p", (void*) c);
}

/*------------------------------------------------------------------------*/

// Almost the same function as 'search_assign' except that we do not pretend
// to learn a new unit clause (which was confusing in log files).

void Internal::assign_original_unit (int lit) {
  assert (!level);
  const int idx = vidx (lit);
  assert (!vals[idx]);
  assert (!flags (idx).eliminated ());
  Var & v = var (idx);
  v.level = level;
  v.trail = (int) trail.size ();
  v.reason = 0;
  const signed char tmp = sign (lit);
  vals[idx] = tmp;
  vals[-idx] = -tmp;
  assert (val (lit) > 0);
  assert (val (-lit) < 0);
  trail.push_back (lit);
  LOG ("original unit assign %d", lit);
  mark_fixed (lit);
  if (propagate ()) return;
  LOG ("propagation of original unit results in conflict");
  learn_empty_clause ();
}

// New clause added through the API, e.g., while parsing a DIMACS file.
//
void Internal::add_new_original_clause () {
  if (level) backtrack ();
  LOG (original, "original clause");
  bool skip = false;
  if (unsat) {
    LOG ("skipping clause since formula already inconsistent");
    skip = true;
  } else {
    assert (clause.empty ());
    for (const auto & lit : original) {
      int tmp = marked (lit);
      if (tmp > 0) {
        LOG ("removing duplicated literal %d", lit);
      } else if (tmp < 0) {
        LOG ("tautological since both %d and %d occur", -lit, lit);
        skip = true;
      } else {
        mark (lit);
        tmp = val (lit);
        if (tmp < 0) {
          LOG ("removing falsified literal %d", lit);
        } else if (tmp > 0) {
          LOG ("satisfied since literal %d true", lit);
          skip = true;
        } else {
          clause.push_back (lit);
          assert (flags (lit).status != Flags::UNUSED);
        }
      }
    }
    for (const auto & lit : original)
      unmark (lit);
  }
  if (skip) {
    if (proof) proof->delete_clause (original);
  } else {
    size_t size = clause.size ();
    if (!size) {
      if (!unsat) {
        if (!original.size ()) VERBOSE (1, "found empty original clause");
        else MSG ("found falsified original clause");
        unsat = true;
      }
    } else if (size == 1) {
      assign_original_unit (clause[0]);
    } else {
      Clause * c = new_clause (false);
      watch_clause (c);
    }
    if (original.size () > size) {
      external->check_learned_clause ();
      if (proof) {
        proof->add_derived_clause (clause);
        proof->delete_clause (original);
      }
    }
  }
  clause.clear ();
}

// Add learned new clause during conflict analysis and watch it. Requires
// that the clause is at least of size 2, and the first two literals
// are assigned at the highest decision level.
//
Clause * Internal::new_learned_redundant_clause (int glue) {
  assert (clause.size () > 1);
#ifndef NDEBUG
  for (size_t i = 2; i < clause.size (); i++)
    assert (var (clause[0]).level >= var (clause[i]).level),
    assert (var (clause[1]).level >= var (clause[i]).level);
#endif
  external->check_learned_clause ();
  Clause * res = new_clause (true, glue);
  if (proof) proof->add_derived_clause (res);
  assert (watching ());
  watch_clause (res);
  return res;
}

// Add hyper binary resolved clause during 'probing'.
//
Clause * Internal::new_hyper_binary_resolved_clause (bool red, int glue) {
  external->check_learned_clause ();
  Clause * res = new_clause (red, glue);
  if (proof) proof->add_derived_clause (res);
  assert (watching ());
  watch_clause (res);
  return res;
}

// Add hyper ternary resolved clause during 'ternary'.
//
Clause * Internal::new_hyper_ternary_resolved_clause (bool red) {
  external->check_learned_clause ();
  size_t size = clause.size ();
  Clause * res = new_clause (red, size);
  if (proof) proof->add_derived_clause (res);
  assert (!watching ());
  return res;
}

// Add a new clause with same glue and redundancy as 'orig' but literals are
// assumed to be in 'clause' in 'decompose' and 'vivify'.
//
Clause * Internal::new_clause_as (const Clause * orig) {
  external->check_learned_clause ();
  const int new_glue = orig->glue;
  Clause * res = new_clause (orig->redundant, new_glue);
  assert (!orig->redundant || !orig->keep || res->keep);
  if (proof) proof->add_derived_clause (res);
  assert (watching ());
  watch_clause (res);
  return res;
}

// Add resolved clause during resolution, e.g., bounded variable
// elimination, but do not connect its occurrences here.
//
Clause * Internal::new_resolved_irredundant_clause () {
  external->check_learned_clause ();
  Clause * res = new_clause (false);
  if (proof) proof->add_derived_clause (res);
  assert (!watching ());
  return res;
}

}
