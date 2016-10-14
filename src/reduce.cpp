#include "internal.hpp"

#include "clause.hpp"
#include "iterator.hpp"
#include "macros.hpp"
#include "proof.hpp"

#include <algorithm>

namespace CaDiCaL {

bool Internal::reducing () {
  if (!opts.reduce) return false;
  return stats.conflicts >= reduce_limit;
}

// Reason clauses (on non-zero decision level) can not be collected.
// We protect them before and unprotect them after garbage collection.

void Internal::protect_reasons () {
  for (const_int_iterator i = trail.begin (); i != trail.end (); i++) {
    Var & v = var (*i);
    if (v.level && v.reason) v.reason->reason = true;
  }
}

void Internal::unprotect_reasons () {
  for (const_int_iterator i = trail.begin (); i != trail.end (); i++) {
    Var & v = var (*i);
    if (v.level && v.reason)
      assert (v.reason->reason), v.reason->reason = false;
  }
}

// Returns 1 if the given clause is root level satisfied or -1 if it is not
// root level satisfied but contains a root level falsified literal and 0
// otherwise, if it does not contain a root level fixed literal.

int Internal::clause_contains_fixed_literal (Clause * c) {
  const int * lits = c->literals, size = c->size;
  int res = 0;
  for (int i = 0; res <= 0 && i < size; i++) {
    const int lit = lits[i];
    const int tmp = fixed (lit);
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
  const int size = c->size;
  int * lits = c->literals, j = 0;
  for (int i = 0; i < size; i++) {
    const int lit = lits[j++] = lits[i];
    const int tmp = fixed (lit);
    assert (tmp <= 0);
    if (tmp >= 0) continue;
    LOG ("flushing %d", lit);
    j--;
  }
  int flushed = c->size - j;
  const size_t bytes = flushed * sizeof (int);
  stats.reduce.bytes += bytes;
  dec_bytes (bytes);
  for (int i = j; i < size; i++) lits[i] = 0;
  c->size = j;
  LOG (c, "flushed %d literals and got", flushed);
}

void Internal::mark_satisfied_clauses_as_garbage () {
  if (fixed_limit >= stats.fixed) return;
  for (const_clause_iterator i = clauses.begin (); i != clauses.end (); i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    const int tmp = clause_contains_fixed_literal (c);
         if (tmp > 0) c->garbage = true;
    else if (tmp < 0) flush_falsified_literals (c);
  }
  fixed_limit = stats.fixed;
}

// Clause with smaller glucose level (glue) are considered more useful.
// Then we use the 'resolved' time stamp as a tie breaker.  So more recently
// resolved clauses are preferred to keep (if they have the same glue).

struct less_usefull {
  bool operator () (Clause * c, Clause * d) {
    if (c->glue > d->glue) return true;
    if (c->glue < d->glue) return false;
    return resolved_earlier () (c, d);
  }
};

// This function implements the important reduction policy. It determines
// which redundant clauses are considered not useful and thus will be
// collected in a subsequent garbage collection phase.

void Internal::mark_useless_redundant_clauses_as_garbage () {
  vector<Clause*> stack;
  stack.reserve (stats.clauses.redundant);
  for (const_clause_iterator i = clauses.begin (); i != clauses.end (); i++) {
    Clause * c = *i;
    if (!c->redundant) continue;            // keep irredundant
    if (c->reason) continue;                // need to keep reasons
    if (c->garbage) continue;               // already marked
    if (c->size <= opts.keepsize) continue; // keep small size clauses
    if (c->glue <= opts.keepglue) continue; // keep small glue clauses
    if (c->resolved () > recently_resolved) continue;
    stack.push_back (c);
  }
  sort (stack.begin (), stack.end (), less_usefull ());
  const_clause_iterator target = stack.begin () + stack.size ()/2;
  for (const_clause_iterator i = stack.begin (); i != target; i++) {
    LOG (*i, "marking useless to be collected");
    (*i)->garbage = true;
  }
}

void Internal::delete_garbage_clauses () {
  const_clause_iterator i = clauses.begin ();
  clause_iterator j = clauses.begin ();
  size_t collected_bytes = 0;
  while (i != clauses.end ()) {
    Clause * c = *j++ = *i++;
    if (c->reason || !c->garbage) continue;
    collected_bytes += delete_clause (c);
    j--;
  }
  clauses.resize (j - clauses.begin ());
  LOG ("collected %ld bytes", collected_bytes);
}

// Deallocate watcher stacks of inactive variables and reset watcher stacks
// of still active variables.

void Internal::flush_watches () {
  size_t current_bytes = 0, max_bytes = 0;
  for (int idx = 1; idx <= max_var; idx++) {
    for (int sign = -1; sign <= 1; sign += 2) {
      const int lit = sign * idx;
      Watches & ws = watches (lit);
      const size_t bytes = ws.capacity () * sizeof ws[0];
      max_bytes += bytes;
      if (ws.empty () || fixed (lit)) ws = Watches ();
      else ws.clear (), current_bytes += bytes;
    }
  }
  stats.bytes.watcher.current = current_bytes;
  if (max_bytes > stats.bytes.watcher.max)
    stats.bytes.watcher.max = max_bytes;
}

void Internal::setup_watches () {
  for (const_clause_iterator i = clauses.begin (); i != clauses.end (); i++)
    watch_clause (*i);
}

void Internal::garbage_collection () {
  delete_garbage_clauses ();
  flush_watches ();
  setup_watches ();
}

void Internal::reduce () {
  START (reduce);
  stats.reduce.count++;
  report ('R', 1);
  protect_reasons ();
  mark_satisfied_clauses_as_garbage ();
  mark_useless_redundant_clauses_as_garbage ();
  garbage_collection ();
  unprotect_reasons ();
  reduce_inc += opts.reduceinc;
  reduce_limit = stats.conflicts + reduce_inc;
  recently_resolved = stats.resolved;
  report ('-');
  STOP (reduce);
}

};
