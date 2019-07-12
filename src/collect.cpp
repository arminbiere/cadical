#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Returns the positive number '1' ( > 0) if the given clause is root level
// satisfied or the negative number '-1' ( < 0) if it is not root level
// satisfied but contains a root level falsified literal. Otherwise, if it
// contains neither a satisfied nor falsified literal, then '0' is returned.

int Internal::clause_contains_fixed_literal (Clause * c) {
  int satisfied = 0, falsified = 0;
  for (const auto & lit : *c) {
    const int tmp = fixed (lit);
    if (tmp > 0) {
      LOG (c, "root level satisfied literal %d in", lit);
      satisfied++;
    }
    if (tmp < 0) {
      LOG (c, "root level falsified literal %d in", lit);
      falsified++;
    }
  }
       if (satisfied) return 1;
  else if (falsified) return -1;
  else                return 0;
}

// Assume that the clause is not root level satisfied but contains a literal
// set to false (root level falsified literal), so it can be shrunken.  The
// clause data is not actually reallocated at this point to avoid dealing
// with issues of special policies for watching binary clauses or whether a
// clause is extended or not. Only its size field is adjusted accordingly
// after flushing out root level falsified literals.

void Internal::remove_falsified_literals (Clause * c) {
  const const_literal_iterator end = c->end ();
  const_literal_iterator i;
  int num_non_false = 0;
  for (i = c->begin (); num_non_false < 2 && i != end; i++)
    if (fixed (*i) >= 0) num_non_false++;
  if (num_non_false < 2) return;
  if (proof) proof->flush_clause (c);
  literal_iterator j = c->begin ();
  for (i = j; i != end; i++) {
    const int lit = *j++ = *i, tmp = fixed (lit);
    assert (tmp <= 0);
    if (tmp >= 0) continue;
    LOG ("flushing %d", lit);
    j--;
  }
  stats.collected += shrink_clause (c, j - c->begin ());
}

// If there are new units (fixed variables) since the last garbage
// collection we go over all clauses, mark satisfied ones as garbage and
// flush falsified literals.  Otherwise if no new units have been generated
// since the last garbage collection just skip this step.

void Internal::mark_satisfied_clauses_as_garbage () {

  if (last.collect.fixed >= stats.all.fixed) return;
  last.collect.fixed = stats.all.fixed;

  LOG ("marking satisfied clauses and removing falsified literals");

  for (const auto & c : clauses) {
    if (c->garbage) continue;
    const int tmp = clause_contains_fixed_literal (c);
         if (tmp > 0) mark_garbage (c);
    else if (tmp < 0) remove_falsified_literals (c);
  }
}

/*------------------------------------------------------------------------*/

// Update occurrence lists before deleting garbage clauses in the context of
// preprocessing, e.g., during bounded variable elimination 'elim'.  The
// result is the number of remaining clauses, which in this context means
// the number of non-garbage clauses.

size_t Internal::flush_occs (int lit) {
  Occs & os = occs (lit);
  const const_occs_iterator end = os.end ();
  occs_iterator j = os.begin ();
  const_occs_iterator i;
  size_t res = 0;
  Clause * c;
  for (i = j; i != end; i++) {
    c = *i;
    if (c->collect ()) continue;
    *j++ = c->moved ? c->copy : c;
    assert (!c->redundant);
    res++;
  }
  os.resize (j - os.begin ());
  shrink_occs (os);
  return res;
}

// Update watch lists before deleting garbage clauses in the context of
// 'reduce' where we watch and no occurrence lists.  We have to protect
// reason clauses not be collected and thus we have this additional check
// hidden in 'Clause.collect', which for the root level context of
// preprocessing is actually redundant.

inline void Internal::flush_watches (int lit, Watches & saved) {
  assert (saved.empty ());
  Watches & ws = watches (lit);
  const const_watch_iterator end = ws.end ();
  watch_iterator j = ws.begin ();
  const_watch_iterator i;
  for (i = j; i != end; i++) {
    Watch w = *i;
    Clause * c = w.clause;
    if (c->collect ()) continue;
    if (c->moved) c = w.clause = c->copy;
    w.size = c->size;
    const int new_blit_pos = (c->literals[0] == lit);
    assert (c->literals[!new_blit_pos] == lit);
    w.blit = c->literals[new_blit_pos];
    if (w.binary ()) *j++ = w;
    else saved.push_back (w);
  }
  ws.resize (j - ws.begin ());
  for (const auto & w : saved) ws.push_back (w);
  saved.clear ();
  shrink_vector (ws);
}

void Internal::flush_all_occs_and_watches () {
  if (occurring ())
    for (int idx = 1; idx <= max_var; idx++)
      flush_occs (idx), flush_occs (-idx);

  if (watching ()) {
    Watches tmp;
    for (int idx = 1; idx <= max_var; idx++)
      flush_watches (idx, tmp), flush_watches (-idx, tmp);
  }
}

/*------------------------------------------------------------------------*/

// This is a simple garbage collector which does not move clauses.  It needs
// less space than the arena based clause allocator, but is not as cache
// efficient, since the copying garbage collector can put clauses together
// which are likely accessed after each other.

void Internal::delete_garbage_clauses () {

  flush_all_occs_and_watches ();

  LOG ("deleting garbage clauses");
  int64_t collected_bytes = 0, collected_clauses = 0;
  const auto end = clauses.end ();
  auto j = clauses.begin (), i = j;
  while (i != end) {
    Clause * c = *j++ = *i++;
    if (!c->collect ()) continue;
    collected_bytes += c->bytes ();
    collected_clauses++;
    delete_clause (c);
    j--;
  }
  clauses.resize (j - clauses.begin ());
  shrink_vector (clauses);

  PHASE ("collect", stats.collections,
    "collected %" PRId64 " bytes of %" PRId64 " garbage clauses",
    collected_bytes, collected_clauses);
}

/*------------------------------------------------------------------------*/

// This is the start of the copying garbage collector using the arena.  At
// the core is the following function, which copies a clause to the 'to'
// space of the arena.  Be careful if this clause is a reason of an
// assignment.  In that case update the reason reference.
//
void Internal::copy_clause (Clause * c) {
  LOG (c, "moving");
  assert (!c->moved);
  char * p = (char*) c, * q = arena.copy (p, c->bytes ());
  Clause * d = c->copy = (Clause *) q;
  LOG ("copied clause[%p] to clause[%p]", c, d);
  if (d->reason) {
    assert (level > 0);
    Var & v = var (d->literals[0]);
    if (v.reason == c) v.reason = d;
    else {
      Var & u = var (d->literals[1]);
      assert (u.reason == c);
      u.reason = d;
    }
  }
  c->moved = true;
}

// This is the moving garbage collector.

void Internal::copy_non_garbage_clauses () {

  size_t collected_clauses = 0, collected_bytes = 0;
  size_t     moved_clauses = 0,     moved_bytes = 0;

  // First determine 'moved_bytes' and 'collected_bytes'.
  //
  for (const auto & c : clauses)
    if (!c->collect ()) moved_bytes += c->bytes (), moved_clauses++;
    else collected_bytes += c->bytes (), collected_clauses++;

  PHASE ("collect", stats.collections,
    "moving %zd bytes %.0f%% of %zd non garbage clauses",
    moved_bytes,
    percent (moved_bytes, collected_bytes + moved_bytes),
    moved_clauses);

  // Prepare 'to' space of size 'moved_bytes'.
  //
  arena.prepare (moved_bytes);

  // Keep clauses in arena in the same order.
  //
  if (opts.arenacompact)
    for (const auto & c : clauses)
      if (!c->collect () && arena.contains (c))
        copy_clause (c);

  if (opts.arenatype == 1 || !watching ()) {

    // Localize according to current clause order.

    // If the option 'opts.arenatype == 1' is set, then this means the
    // solver uses the original order of clauses.  If there are no watches,
    // we can not use the watched based copying policies below.  This
    // happens if garbage collection is triggered during bounded variable
    // elimination.

    // Copy clauses according to the order of calling 'copy_clause', which
    // in essence just gives a compacting garbage collector, since their
    // relative order is kept, and actually already gives the largest
    // benefit due to better cache locality.

    for (const auto & c : clauses)
      if (!c->moved && !c->collect ())
        copy_clause (c);

  } else if (opts.arenatype == 2) {

    // Localize according to (original) variable order.

    // This is almost the version used by MiniSAT and descendants.
    // Our version uses saved phases too.

    for (int sign = -1; sign <= 1; sign += 2)
      for (int idx = 1; idx <= max_var; idx++)
        for (const auto & w : watches (sign * likely_phase (idx)))
          if (!w.clause->moved && !w.clause->collect ())
            copy_clause (w.clause);

  } else {

    // Localize according to decision queue order.

    // This is the default for search. It allocates clauses in the order of
    // the decision queue and also uses saved phases.  It seems faster than
    // the MiniSAT version and thus we keep 'opts.arenatype == 3'.

    assert (opts.arenatype == 3);

    for (int sign = -1; sign <= 1; sign += 2)
      for (int idx = queue.last; idx; idx = link (idx).prev)
        for (const auto & w : watches (sign * likely_phase (idx)))
          if (!w.clause->moved && !w.clause->collect ())
            copy_clause (w.clause);
  }

  // Do not forget to move clauses which are not watched, which happened in
  // a rare situation, and now is only left as defensive code.
  //
  for (const auto & c : clauses)
    if (!c->collect () && !c->moved)
      copy_clause (c);

  // Update watches or occurrence lists.
  //
  flush_all_occs_and_watches ();

  // Replace and flush clause references in 'clauses'.
  //
  const auto end = clauses.end ();
  auto j = clauses.begin (), i = j;
  for (; i != end; i++) {
    Clause * c = *i;
    if (c->collect ()) delete_clause (c);
    else assert (c->moved), *j++ = c->copy, deallocate_clause (c);
  }
  clauses.resize (j - clauses.begin ());
  if (clauses.size () < clauses.capacity ()/2) shrink_vector (clauses);

  if (opts.arenasort)
    rsort (clauses.begin (), clauses.end (), pointer_rank ());

  // Release 'from' space completely and then swap 'to' with 'from'.
  //
  arena.swap ();

  PHASE ("collect", stats.collections,
    "collected %zd bytes %.0f%% of %zd garbage clauses",
    collected_bytes,
    percent (collected_bytes, collected_bytes + moved_bytes),
    collected_clauses);
}

/*------------------------------------------------------------------------*/

// Maintaining clause statistics is complex and error prone but necessary
// for proper scheduling of garbage collection, particularly during bounded
// variable elimination.  With this function we can check whether these
// statistics are updated correctly.

void Internal::check_clause_stats () {
#ifndef NDEBUG
  int64_t irredundant = 0, redundant = 0, total = 0, irrbytes = 0;
  for (const auto & c : clauses) {
    if (c->garbage) continue;
    if (c->redundant) redundant++; else irredundant++;
    if (!c->redundant) irrbytes += c->bytes ();
    total++;
  }
  assert (stats.current.irredundant == irredundant);
  assert (stats.current.redundant == redundant);
  assert (stats.current.total == total);
  assert (stats.irrbytes == irrbytes);
#endif
}

/*------------------------------------------------------------------------*/

bool Internal::arenaing () {
  return opts.arena && (stats.collections > 1);
}

void Internal::garbage_collection () {
  if (unsat) return;
  START (collect);
  report ('G', 1);
  stats.collections++;
  mark_satisfied_clauses_as_garbage ();
  if (arenaing ()) copy_non_garbage_clauses ();
  else delete_garbage_clauses ();
  check_clause_stats ();
  check_var_stats ();
  report ('C', 1);
  STOP (collect);
}

}
