#include "internal.hpp"
#include "iterator.hpp"
#include "clause.hpp"
#include "message.hpp"
#include "macros.hpp"
#include "proof.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Returns 1 if the given clause is root level satisfied or -1 if it is not
// root level satisfied but contains a root level falsified literal and 0
// otherwise, if it does not contain a root level fixed literal.

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

void Internal::flush_falsified_literals (Clause * c) {
  if (c->reason || c->size == 2) return;
  if (proof) proof->trace_flushing_clause (c);
  const const_literal_iterator end = c->end ();
  const_literal_iterator i = c->begin ();
  literal_iterator j = c->begin ();
  while (i != end) {
    const int lit = *j++ = *i++, tmp = fixed (lit);
    assert (tmp <= 0);
    if (tmp >= 0) continue;
    LOG ("flushing %d", lit);
    j--;
  }
  c->size = j - c->begin ();
  int flushed = end - j;
  const size_t bytes = flushed * sizeof (int);
  stats.collected += bytes;
  while (j != end) *j++ = 0;
  dec_bytes (bytes);
  LOG (c, "flushed %d literals and got", flushed);
}

void Internal::mark_satisfied_clauses_as_garbage () {

  // Only needed if there are new units (fixed variables) since last time.
  //
  if (lim.fixed_at_last_collect >= stats.fixed) return;

  const_clause_iterator i;
  for (i = clauses.begin (); i != clauses.end (); i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    const int tmp = clause_contains_fixed_literal (c);
         if (tmp > 0) mark_garbage (c);
    else if (tmp < 0) flush_falsified_literals (c);
  }

  lim.fixed_at_last_collect = stats.fixed;
}

/*------------------------------------------------------------------------*/

void Internal::flush_clause_references (vector<Clause *> & v) {
  const const_clause_iterator end = v.end ();
  clause_iterator j = v.begin ();
  const_clause_iterator i;
  for (i = j; i != end; i++) {
    Clause * c = *i;
    if (!c->collect ()) *j++ = c;
  }
  v.resize (j - v.begin ());
  shrink_vector (v);
}

// This is a simple garbage collector which does not move clauses.

void Internal::delete_garbage_clauses () {

  LOG ("deleting garbage clauses");

  if (occs)
    for (int lit = -max_var; lit <= max_var; lit++)
      if (lit) flush_clause_references (occs[lit]);

  const_clause_iterator i = clauses.begin ();
  clause_iterator j = clauses.begin ();
  size_t collected_bytes = 0;
  while (i != clauses.end ()) {
    Clause * c = *j++ = *i++;
    if (!c->collect ()) continue;
    collected_bytes += c->bytes ();
    delete_clause (c);
    j--;
  }
  clauses.resize (j - clauses.begin ());

  VRB ("collect", stats.collections,
    "collected %ld bytes", (long) collected_bytes);
}

/*------------------------------------------------------------------------*/

void Internal::flush_and_copy_clause_references (vector<Clause *> & v) {
  const const_clause_iterator end = v.end ();
  clause_iterator j = v.begin ();
  const_clause_iterator i;
  for (i = j; i != end; i++) {
    Clause * c = *i;
    if (c->collect ()) continue;
    assert (c->moved);
    *j++ = c->copy;
  }
  v.resize (j - v.begin ());
  shrink_vector (v);
}

// Copy a clause to the 'to' space of the arena.  Be careful if this clause
// is a reason of an assignment.  In that case update the reason reference.
//
void Internal::move_clause (Clause * c) {
  LOG (c, "moving");
  assert (!c->moved);
  char * p = c->start (), * q = arena.copy (p, c->bytes ());
  Clause * d = c->copy = (Clause *) (q - c->offset ());
  if (d->reason) var (d->literals[val (d->literals[1]) > 0]).reason = d;
  c->moved = true;
}

// This is the moving garbage collector.

void Internal::move_non_garbage_clauses () {

  Clause * c;

  size_t collected_clauses = 0, collected_bytes = 0;
  size_t     moved_clauses = 0,     moved_bytes = 0;

  // First determine 'moved_bytes' and 'collected_bytes'.
  //
  const_clause_iterator i;
  for (i = clauses.begin (); i != clauses.end (); i++)
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

  // Copy clauses according to the order of calling 'move_clause', which in
  // essence just gives a compacting garbage collector, since their
  // relative order is kept, and already gives some cache locality.
  //
  if (opts.arena == 1) {

    // Localize according to (original) clause order.

    for (i = clauses.begin (); i != clauses.end (); i++)
      if (!(c = *i)->collect ()) move_clause (c);

  } else if (opts.arena == 2) {

    // Localize according to (original) variable order.

    for (int sign = -1; sign <= 1; sign += 2) {
      for (int idx = 1; idx <= max_var; idx++) {
        const Watches & ws = watches (sign * phases[idx] * idx);
        for (const_watch_iterator i = ws.begin (); i != ws. end (); i++)
          if (!(c = i->clause)->moved && !c->collect ()) move_clause (c);
      }
    }

  } else {

    // Localize according to decision queue order.

    assert (opts.arena == 3);

    for (int sign = -1; sign <= 1; sign += 2) {
      for (int idx = queue.last; idx; idx = link (idx).prev) {
        const Watches & ws = watches (sign * phases[idx] * idx);
        for (const_watch_iterator i = ws.begin (); i != ws. end (); i++)
          if (!(c = i->clause)->moved && !c->collect ()) move_clause (c);
      }
    }
  }

  if (occs)
    for (int lit = -max_var; lit <= max_var; lit++)
      if (lit) flush_and_copy_clause_references (occs[lit]);

  // Replace and flush clause references in 'clauses'.
  //
  clause_iterator j = clauses.begin ();
  for (i = j; i != clauses.end (); i++) {
    if ((c = *i)->collect ()) delete_clause (c);
    else assert (c->moved), *j++ = c->copy, deallocate_clause (c);
  }
  clauses.resize (j - clauses.begin ());

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

// Deallocate watcher stacks of inactive (fixed) variables and reset watcher
// stacks. As a side effect of this function the actual maximum memory for
// watcher stacks is computed and the corresponding statistics are updated.

void Internal::flush_watches () {
  size_t max_bytes = 0;
  for (int idx = 1; idx <= max_var; idx++) {
    for (int sign = -1; sign <= 1; sign += 2) {
      const int lit = sign * idx;
      Watches & ws = watches (lit);
      max_bytes += bytes_vector (ws);;
      erase_vector (ws);
    }
  }
  if (max_bytes > stats.bytes.watcher.max)
    stats.bytes.watcher.max = max_bytes;
}

// Add back all the watches and again compute current memory used.

void Internal::setup_watches () {
  const const_clause_iterator end = clauses.end ();
  const_clause_iterator i;
  for (i = clauses.begin (); i != end; i++)
    watch_clause (*i);

  size_t current_bytes = 0;
  for (int lit = -max_var; lit <= max_var; lit++)
    current_bytes += bytes_vector (watches (lit));
  stats.bytes.watcher.current = current_bytes;
  if (current_bytes > stats.bytes.watcher.max)
    stats.bytes.watcher.max = current_bytes;
}

/*------------------------------------------------------------------------*/

void Internal::check_clause_stats () {
#ifndef NDEBUG
  long irredundant = 0, redundant = 0;
  const const_clause_iterator end = clauses.end ();
  const_clause_iterator i;
  for (i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    if (c->redundant) redundant++; else irredundant++;
  }
  assert (stats.irredundant == irredundant);
  assert (stats.redundant == redundant);
#endif
}

/*------------------------------------------------------------------------*/

void Internal::garbage_collection () {
  START (collect);
  stats.collections++;
  mark_satisfied_clauses_as_garbage ();
  if (opts.arena) move_non_garbage_clauses ();
  else delete_garbage_clauses ();
  check_clause_stats ();
  flush_watches ();
  setup_watches ();
  STOP (collect);
}

};
