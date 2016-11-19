#include "internal.hpp"

#include "clause.hpp"
#include "macros.hpp"
#include "message.hpp"
#include "proof.hpp"

#include <algorithm>

namespace CaDiCaL {

void Internal::watch_clause (Clause * c) {
  const int size = c->size;
  const int l0 = c->literals[0];
  const int l1 = c->literals[1];
  watch_literal (l0, l1, c, size);
  watch_literal (l1, l0, c, size);
}

/*------------------------------------------------------------------------*/

// Since the literals are embedded a clause actually contains always 'size'
// literals and 'literals[2]' should be regarded as 'literals[size]'.
// Clauses have at least 2 literals.  Empty and unit clauses are implicitly
// handled and never allocated.

size_t Internal::bytes_clause (int size) {
  return sizeof (Clause) + (size - 2) * sizeof (int);
}

// Redundant clauses of large glue and large size are extended to hold a
// 'analyzed' time stamp.  This makes memory allocation and deallocation a
// little bit tricky but saves space and time.  Since the embedding of the
// literals is really important and on the same level of complexity we keep
// both optimizations.

Clause * Internal::new_clause (bool red, int glue) {
  if (glue > MAX_GLUE) glue = MAX_GLUE;
  assert (clause.size () <= (size_t) INT_MAX);
  const int size = (int) clause.size ();  assert (size >= 2);
  size_t bytes = bytes_clause (size);
  bool extended = (red && size > opts.keepsize && glue > opts.keepglue);
  if (!extended) bytes -= EXTENDED_OFFSET;
  char * ptr = new char[bytes];
  if (!extended) ptr -= EXTENDED_OFFSET;
  Clause * res = (Clause*) ptr;
  res->extended = extended;
  res->redundant = red;
  res->garbage = false;
  res->reason = false;
  res->moved = false;
  res->glue = glue;
  res->size = size;
  res->pos = 2;
  for (int i = 0; i < size; i++) res->literals[i] = clause[i];
  if (extended) res->analyzed () = ++stats.analyzed;
  clauses.push_back (res);
  if (red) stats.redundant++; else stats.irredundant++;
  LOG (res, "new");
  return res;
}

// This is the 'raw' deallocation of a clause.  If the clause is in the
// arena nothing happens.  If the clause is not in the arena and its memory
// is reclaimed immediately and the allocation statistics is updated.

void Internal::deallocate_clause (Clause * c) {
  char * p = c->start ();
  if (arena.contains (p)) return;
  LOG (c, "deallocate");
  delete [] p;
}

void Internal::delete_clause (Clause * c) {
  LOG (c, "delete");
  size_t bytes = c->bytes ();
  stats.collected += bytes;
  if (c->garbage) assert (stats.garbage > 0), stats.garbage--;
  if (proof) proof->trace_delete_clause (c);
  deallocate_clause (c);
}

void Internal::touch_clause (Clause * c) {
  assert (!c->redundant);
  const const_literal_iterator end = c->end ();
  const_literal_iterator i;
  for (i = c->begin (); i != end; i++)
    touched (*i) = ++stats.touched;
}

// We want to eagerly update statistics as soon clauses are marked garbage.
// Otherwise 'report' for instance gives wrong numbers after 'subsume'
// before the next 'reduce'.  Thus we factored out marking and accounting
// for garbage clauses.  Note that we do not update allocated bytes
// statistics at this point, but wait until the next 'collect'.  In order
// not to miss any update to those statistics we call 'check_clause_stats'
// after garbage collection in debugging mode.  This is also the place where
// we touch variables in irredundant clauses which became garbage.
//
void Internal::mark_garbage (Clause * c) {
  assert (!c->garbage);
  if (c->redundant) assert (stats.redundant), stats.redundant--;
  else assert (stats.irredundant), stats.irredundant--;
  stats.garbage++;
  c->garbage = true;
  if (!c->redundant) touch_clause (c);
}

bool Internal::tautological_clause () {
  sort (clause.begin (), clause.end (), lit_less_than ());
  const_int_iterator i = clause.begin ();
  int_iterator j = clause.begin ();
  int prev = 0;
  while (i != clause.end ()) {
    int lit = *i++;
    if (lit == -prev) return true;
    if (lit !=  prev) *j++ = prev = lit;
  }
  if (j != clause.end ()) {
    LOG ("removing %d duplicates", (long)(clause.end () - j));
    clause.resize (j - clause.begin ());
  }
  return false;
}

void Internal::add_new_original_clause () {
  int size = (int) clause.size ();
  if (!size) {
    if (!unsat) {
      MSG ("original empty clause");
      unsat = true;
    } else LOG ("original empty clause produces another inconsistency");
  } else if (size == 1) {
    int unit = clause[0], tmp = val (unit);
    if (!tmp) assign_unit (unit);
    else if (tmp < 0) {
      if (!unsat) {
        MSG ("parsed clashing unit");
        clashing = true;
      } else LOG ("original clashing unit produces another inconsistency");
    } else LOG ("original redundant unit");
  } else watch_clause (new_clause (false));
}

Clause * Internal::new_learned_redundant_clause (int glue) {
  Clause * res = new_clause (true, glue);
  if (proof) proof->trace_add_clause (res);
  watch_clause (res);
  return res;
}

Clause * Internal::new_resolved_irredundant_clause () {
  Clause * res = new_clause (false);
  if (proof) proof->trace_add_clause (res);
  assert (!watches ());
  return res;
}

};
