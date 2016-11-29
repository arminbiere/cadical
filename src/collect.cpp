#include "internal.hpp"
#include "iterator.hpp"
#include "clause.hpp"
#include "message.hpp"
#include "macros.hpp"
#include "proof.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Returns positive number 1 ( > 0) if the given clause is root level
// satisfied or the negative number -1 ( < 0) if it is not root level
// satisfied but contains a root level falsified literal and 0 otherwise, if
// it does not contain a root level fixed literal.

int Internal::clause_contains_fixed_literal (Clause * c) {
  const const_literal_iterator end = c->end ();
  const_literal_iterator i = c->begin ();
  int res = 0;
  while (res <= 0 && i != end) {
    const int lit = *i++, tmp = fixed (lit);
    if (tmp > 0) {
      LOG (c, "root level satisfied literal %d in", lit);
      res = 1;
    } else if (!res && tmp < 0) {
      LOG (c, "root level falsified literal %d in", lit);
      res = -1;
    }
  }
  return res;
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
  if (proof) proof->trace_flushing_clause (c);
  literal_iterator j = c->begin ();
  for (i = j; i != end; i++) {
    const int lit = *j++ = *i, tmp = fixed (lit);
    assert (tmp <= 0);
    if (tmp >= 0) continue;
    LOG ("flushing %d", lit);
    j--;
  }
  c->size = j - c->begin ();
  c->update_after_shrinking ();
  int flushed = end - j;
  const size_t bytes = flushed * sizeof (int);
  if (!c->redundant) {
    assert (stats.irrbytes >= (long) bytes);
    stats.irrbytes -= bytes;
  }
  stats.collected += bytes;
#ifndef NDEBUG
  while (j != end) *j++ = 0;
#endif
  LOG (c, "flushed %d literals and got", flushed);
  if (likely_to_be_kept_clause (c)) mark_added (c);
}

void Internal::mark_satisfied_clauses_as_garbage () {

  // Only needed if there are new units (fixed variables) since last time.
  //
  if (lim.fixed_at_last_collect >= stats.fixed) return;
  lim.fixed_at_last_collect = stats.fixed;

  LOG ("marking satisfied clauses and removing falsified literals");

  const_clause_iterator i;
  for (i = clauses.begin (); i != clauses.end (); i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    const int tmp = clause_contains_fixed_literal (c);
         if (tmp > 0) mark_garbage (c);
    else if (tmp < 0) remove_falsified_literals (c);
  }
}

/*------------------------------------------------------------------------*/

// Update occurrence and watch lists before removing garbage clauses.  This
// works both in the context of 'reduce' where the decision level might be
// non zero as well as during preprocessing, e.g., in 'elim'.  During
// 'reduce' we have to protect reason clauses not be collected and thus we
// have this additional check hidden in 'Clause.collect', which for the root
// level context of preprocessing is actually redundant.

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
    if (!c->redundant) res++;
  }
  os.resize (j - os.begin ());
  shrink_occs (os);
  return res;
}

void Internal::flush_watches (int lit) {
  Watches & ws = watches (lit);
  const const_watch_iterator end = ws.end ();
  watch_iterator j = ws.begin ();
  const_watch_iterator i;
  for (i = j; i != end; i++) {
    Watch w = *i;
    Clause * c = w.clause;
    if (c->collect ()) continue;
    if (c->moved) c = w.clause = c->copy;
    if (c->size < w.size) {

      // During 'reduce' root level falsified literals might be removed in
      // which case the actual clause size does not match the saved size in
      // the watch lists.  If this is the case we update both size and then
      // eagerly the blocking literal (even if it got not removed). Note
      // that if the clause size and watch list size match, then there is no
      // need to update the watch, except if the clause was moved.

      w.size = c->size;
      const int new_blit_pos = (c->literals[0] == lit);
      assert (c->literals[!new_blit_pos] == lit);
      w.blit = c->literals[new_blit_pos];

    } else assert (c->size == w.size);
    *j++ = w;
  }
  ws.resize (j - ws.begin ());
  shrink_watches (ws);
}

void Internal::flush_all_occs_and_watches () {
  if (occs ())
    for (int idx = 1; idx <= max_var; idx++)
      flush_occs (idx), flush_occs (-idx);

  if (watches ())
    for (int idx = 1; idx <= max_var; idx++)
      flush_watches (idx), flush_watches (-idx);
}

/*------------------------------------------------------------------------*/

// This is a simple garbage collector which does not move clauses.

void Internal::delete_garbage_clauses () {

  flush_all_occs_and_watches ();

  LOG ("deleting garbage clauses");
  long collected_bytes = 0, collected_clauses = 0;
  const const_clause_iterator end = clauses.end ();
  clause_iterator j = clauses.begin ();
  const_clause_iterator i = j;
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

  VRB ("collect", stats.collections,
    "collected %ld bytes of %ld garbage clauses",
    collected_bytes, collected_clauses);
}

/*------------------------------------------------------------------------*/

// Copy a clause to the 'to' space of the arena.  Be careful if this clause
// is a reason of an assignment.  In that case update the reason reference.
//
void Internal::copy_clause (Clause * c) {
  LOG (c, "moving");
  assert (!c->moved);
  char * p = c->start (), * q = arena.copy (p, c->bytes ());
  Clause * d = c->copy = (Clause *) (q - c->offset ());
  if (d->reason) var (d->literals[val (d->literals[1]) > 0]).reason = d;
  c->moved = true;
}

// This is the moving garbage collector.

void Internal::copy_non_garbage_clauses () {

  Clause * c;

  size_t collected_clauses = 0, collected_bytes = 0;
  size_t     moved_clauses = 0,     moved_bytes = 0;

  // First determine 'moved_bytes' and 'collected_bytes'.
  //
  const const_clause_iterator end = clauses.end ();
  const_clause_iterator i;
  for (i = clauses.begin (); i != end; i++)
    if (!(c = *i)->collect ()) moved_bytes += c->bytes (), moved_clauses++;
    else collected_bytes += c->bytes (), collected_clauses++;

  VRB ("collect", stats.collections,
    "moving %ld bytes %.0f%% of %ld non garbage clauses",
    (long) moved_bytes,
    percent (moved_bytes, collected_bytes + moved_bytes),
    (long) moved_clauses);

  // Prepare 'to' space of size 'moved_bytes'.
  //
  arena.prepare (moved_bytes);

  // Copy clauses according to the order of calling 'copy_clause', which in
  // essence just gives a compacting garbage collector, since their
  // relative order is kept, and already gives some cache locality.
  //
  if (opts.arena == 1 || !watches ()) {

    // Localize according to (original) clause order.

    for (i = clauses.begin (); i != end; i++)
      if (!(c = *i)->collect ()) copy_clause (c);

  } else if (opts.arena == 2) {

    // Localize according to (original) variable order.

    for (int sign = -1; sign <= 1; sign += 2) {
      for (int idx = 1; idx <= max_var; idx++) {
        const Watches & ws = watches (sign * phases[idx] * idx);
        const const_watch_iterator ew = ws.end ();
        for (const_watch_iterator i = ws.begin (); i != ew; i++)
          if (!(c = i->clause)->moved && !c->collect ()) copy_clause (c);
      }
    }

  } else {

    // Localize according to decision queue order.

    assert (opts.arena == 3);

    for (int sign = -1; sign <= 1; sign += 2) {
      for (int idx = queue.last; idx; idx = link (idx).prev) {
        const Watches & ws = watches (sign * phases[idx] * idx);
        const const_watch_iterator ew = ws.end ();
        for (const_watch_iterator i = ws.begin (); i != ew; i++)
          if (!(c = i->clause)->moved && !c->collect ()) copy_clause (c);
      }
    }
  }

  // Do not forget to move clauses which are not watched.
  //
  for (i = clauses.begin (); i != end; i++)
    if (!(c = *i)->collect () && !c->moved) copy_clause (c);

  flush_all_occs_and_watches ();

  // Replace and flush clause references in 'clauses'.
  //
  clause_iterator j = clauses.begin ();
  assert (end == clauses.end ());
  for (i = j; i != end; i++) {
    if ((c = *i)->collect ()) delete_clause (c);
    else assert (c->moved), *j++ = c->copy, deallocate_clause (c);
  }
  clauses.resize (j - clauses.begin ());
  shrink_vector (clauses);

  // Release 'from' space completely and then swap 'to' with 'from'.
  //
  arena.swap ();

  VRB ("collect", stats.collections,
    "collected %ld bytes %.0f%% of %ld garbage clauses",
    (long) collected_bytes,
    percent (collected_bytes, collected_bytes + moved_bytes),
    (long) collected_clauses);
}

/*------------------------------------------------------------------------*/

void Internal::check_clause_stats () {
#ifndef NDEBUG
  long irredundant = 0, redundant = 0, blocked = 0;
  size_t irrbytes = 0;
  const const_clause_iterator end = clauses.end ();
  const_clause_iterator i;
  for (i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    if (c->redundant) redundant++; else irredundant++;
    if (c->blocked) blocked++;
    if (!c->redundant) irrbytes += c->bytes ();
  }
  assert (stats.irredundant == irredundant);
  assert (stats.redundant == redundant);
  assert (stats.redblocked == blocked);
#endif
}

/*------------------------------------------------------------------------*/

void Internal::garbage_collection () {
  if (unsat) return;
  START (collect);
  report ('g', 1);
  stats.collections++;
  mark_satisfied_clauses_as_garbage ();
  if (opts.arena) copy_non_garbage_clauses ();
  else delete_garbage_clauses ();
  check_clause_stats ();
  report ('c', 1);
  STOP (collect);
}

};
