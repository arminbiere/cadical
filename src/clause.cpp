#include "internal.hpp"

#include "clause.hpp"
#include "macros.hpp"
#include "message.hpp"
#include "proof.hpp"

#include <algorithm>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Add two watches to a clause.  This is used initially  during allocation
// of a clause and during connecting back all watches after preprocessing.
// Since that happens quite infrequently (in contrast to 'watch_literal'
// called from 'propagate') we can keep this function here.

void Internal::watch_clause (Clause * c) {
  const int size = c->size;
  const int l0 = c->literals[0];
  const int l1 = c->literals[1];
  watch_literal (l0, l1, c, size);
  watch_literal (l1, l0, c, size);
}

/*------------------------------------------------------------------------*/

// Sigend mark or unmark a clause or the global 'clause'.

void Internal::mark (Clause * c) {
  const const_literal_iterator end = c->end ();
  const_literal_iterator k;
  for (k = c->begin (); k != end; k++) mark (*k);
}

void Internal::unmark (Clause * c) {
  const const_literal_iterator end = c->end ();
  const_literal_iterator k;
  for (k = c->begin (); k != end; k++) unmark (*k);
}

void Internal::mark_clause () {
  const const_int_iterator end = clause.end ();
  const_int_iterator k;
  for (k = clause.begin (); k != end; k++) mark (*k);
}

void Internal::unmark_clause () {
  const const_int_iterator end = clause.end ();
  const_int_iterator k;
  for (k = clause.begin (); k != end; k++) unmark (*k);
}

/*------------------------------------------------------------------------*/

// Mark the variables of an irredundant clause to 'have been removed', which
// will trigger these variables to be considered again in the next bounded
// variable elimination phase.  This is called from 'mark_garbage' below.

#ifndef BCE
inline
#endif
void Internal::mark_removed (Clause * c, int except) {
  LOG (c, "marking removed");
  assert (!c->redundant);
  const const_literal_iterator end = c->end ();
  const_literal_iterator i;
  for (i = c->begin (); i != end; i++)
    if (*i != except) mark_removed (*i);
}

// Mark the variables of a (redundant or irredundant) clause to 'have been
// added', which triggers clauses with such a variables, to be considered
// both as a subsumed or subsuming clause in the next subsumption phase.
// This function is called from 'new_clause' below as well as in situations
// where a clause is shrunken (and thus needs to be at least considered
// again to subsume a larger clause).

void Internal::mark_added (Clause * c) {
  LOG (c, "marking added");
  assert (likely_to_be_kept_clause (c));
  const const_literal_iterator end = c->end ();
  const_literal_iterator i;
  for (i = c->begin (); i != end; i++)
    mark_added (*i);
}

/*------------------------------------------------------------------------*/

// Redundant clauses of large glue and large size are extended to hold a
// '_analyzed' time stamp, and similarly longer clauses need a '_pos' field.
// This makes memory allocation and deallocation a little bit tricky but
// saves space and time.  Since the embedding of the literals is really
// important and on the same level of complexity we keep both optimizations.

Clause * Internal::new_clause (bool red, int glue) {

  assert (clause.size () <= (size_t) INT_MAX);
  const int size = (int) clause.size ();
  assert (size >= 2);

  // Since 'glue' is a bit-field, we cap the 'glue' value at 'MAX_GLUE'.
  //
  if (glue > MAX_GLUE) glue = MAX_GLUE;

  // Determine whether this clauses uses a '_pos' and '_analyzed' field.
  //
  bool have_pos, have_analyzed;
  if (!red) have_analyzed = false;
  else if (size <= opts.keepsize) have_analyzed = false;
  else if (glue <= opts.keepglue) have_analyzed = false;
  else have_analyzed = true;
  if (have_analyzed) have_pos = true;
  else have_pos = (size >= opts.posize);

  // Now allocate the clause after ignored the 'offset' bytes, if '_pos' or
  // 'analyzed' fields are not used.
  //
  Clause * c;
  size_t offset = 0;
  if (!have_pos) offset += sizeof c->_pos;
  if (!have_analyzed) offset += sizeof c->_analyzed;
  size_t bytes = sizeof (Clause) + (size - 2) * sizeof (int) - offset;
  char * ptr = new char[bytes];
  ptr -= offset;
  c = (Clause*) ptr;

  // Initialize all clause data and copy literals from global 'clause'.
  //
  if (have_analyzed) c->_analyzed = ++stats.analyzed;
  if (have_pos) c->_pos = 2;
  c->have.analyzed = have_analyzed;
  c->have.pos = have_pos;
  c->redundant = red;
  c->garbage = false;
  c->reason = false;
  c->moved = false;
#ifdef BCE
  c->blocked = false;
#endif
  c->glue = glue;
  c->size = size;
  for (int i = 0; i < size; i++) c->literals[i] = clause[i];

  assert (c->offset () == offset);

  if (red) stats.redundant++;
  else stats.irredundant++, stats.irrbytes += bytes;

  clauses.push_back (c);
  LOG (c, "new");

  if (likely_to_be_kept_clause (c)) mark_added (c);

  return c;
}

// This is the 'raw' deallocation of a clause.  If the clause is in the
// arena nothing happens.  If the clause is not in the arena its memory is
// reclaimed immediately.

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
  if (c->garbage) {
    assert (stats.garbage >= (long) bytes);
    stats.garbage -= bytes;
  }
  if (proof) proof->trace_delete_clause (c);
  deallocate_clause (c);
}

// We want to eagerly update statistics as soon clauses are marked garbage.
// Otherwise 'report' for instance gives wrong numbers after 'subsume'
// before the next 'reduce'.  Thus we factored out marking and accounting
// for garbage clauses.
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
  size_t bytes = c->bytes ();
  if (c->redundant) {
    assert (stats.redundant > 0);
    stats.redundant--;
#ifdef BCE
    if (c->blocked) {
      assert (stats.redblocked > 0);
      stats.redblocked--;
    }
#endif
  } else {
#ifdef BCE
    assert (!c->blocked);
#endif
    assert (stats.irredundant > 0);
    assert (stats.irrbytes >= (long) bytes);
    stats.irrbytes -= bytes;
    stats.irredundant--;
    mark_removed (c);
  }
  stats.garbage += bytes;
  c->garbage = true;
}

/*------------------------------------------------------------------------*/

// Check whether the next to be allocated 'clause' is actually tautological.
// This is currently only used during adding original clauses (through the
// API, e.g., while parsing the DIMACS file in the stand-alone solver).

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

/*------------------------------------------------------------------------*/

// New clause added through the API, e.g., while parsing a DIMACS file.
// Assume the clause has been simplified and checked with
// 'tautological_clause' before.
//
void Internal::add_new_original_clause () {
  stats.original++;
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

// Add learned new clause during conflict analysis and watch it. Requires
// that the clause is at least of size 2, and the first two literals
// are assigned at the highest decision level.
//
Clause * Internal::new_learned_redundant_clause (int glue) {
  Clause * res = new_clause (true, glue);
  if (proof) proof->trace_add_clause (res);
  assert (watches ());
  watch_clause (res);
  return res;
}

// Add resolved clause during resolution, e.g., bounded variable
// elimination, but do not connect its occurrences here.
//
Clause * Internal::new_resolved_irredundant_clause () {
  Clause * res = new_clause (false);
  if (proof) proof->trace_add_clause (res);
  assert (!watches ());
  return res;
}

};
