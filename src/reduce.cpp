#include "solver.hpp"

#include <algorithm>

namespace CaDiCaL {

bool Solver::reducing () {
  if (!opts.reduce) return false;
  return stats.conflicts >= reduce_limit;
}

void Solver::protect_reasons () {
  for (size_t i = 0; i < trail.size (); i++) {
    Var & v = var (trail[i]);
    if (v.level && v.reason) v.reason->reason = true;
  }
}

void Solver::unprotect_reasons () {
  for (size_t i = 0; i < trail.size (); i++) {
    Var & v = var (trail[i]);
    if (v.level && v.reason)
      assert (v.reason->reason), v.reason->reason = false;
  }
}

// Returns 1 if the given clause is root level satisfied or -1 if it is not
// root level satisfied but contains a root level falsified literal and 0
// otherwise, if it does not contain a root level fixed literal.

int Solver::clause_contains_fixed_literal (Clause * c) {
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

void Solver::flush_falsified_literals (Clause * c) {
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

void Solver::mark_satisfied_clauses_as_garbage () {
  if (fixed_limit >= stats.fixed) return;
  for (size_t i = 0; i < clauses.size (); i++) {
    Clause * c = clauses[i];
    if (c->garbage) continue;
    const int tmp = clause_contains_fixed_literal (c);
         if (tmp > 0) c->garbage = true;
    else if (tmp < 0) flush_falsified_literals (c);
  }
  fixed_limit = stats.fixed;
}

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

void Solver::mark_useless_redundant_clauses_as_garbage () {
  vector<Clause*> stack;
  assert (stack.empty ());
  for (size_t i = 0; i < clauses.size (); i++) {
    Clause * c = clauses[i];
    if (!c->redundant) continue;                // keep irredundant
    if (c->reason) continue;                    // need to keep reasons
    if (c->garbage) continue;                   // already marked
    if (c->size <= opts.keepsize) continue;     // keep small size clauses
    if (c->glue <= opts.keepglue) continue;     // keep small glue clauses
    if (c->resolved > recently_resolved) continue; // keep recently resolved
    stack.push_back (c);
  }
  sort (stack.begin (), stack.end (), less_usefull ());
  const size_t target = stack.size ()/2;
  for (size_t i = 0; i < target; i++) {
    LOG (stack[i], "marking useless to be collected");
    stack[i]->garbage = true;
  }
}

void Solver::delete_garbage_clauses () {
  size_t collected_bytes = 0, j = 0;
  for (size_t i = 0; i < clauses.size (); i++) {
    Clause * c = clauses[j++] = clauses[i];
    if (c->reason || !c->garbage) continue;
    collected_bytes += delete_clause (c);
    j--;
  }
  clauses.resize (j);
  LOG ("collected %ld bytes", collected_bytes);
}

void Solver::flush_watches () {
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

void Solver::setup_watches () {
  for (size_t i = 0; i < clauses.size (); i++)
    watch_clause (clauses[i]);
}

void Solver::garbage_collection () {
  delete_garbage_clauses ();
  flush_watches ();
  setup_watches ();
}

void Solver::reduce () {
  START (reduce);
  stats.reduce.count++;
  LOG ("reduce %ld resolved limit %ld", stats.reduce.count, reduce_limit);
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
