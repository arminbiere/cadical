#include "internal.hpp"

#include "clause.hpp"
#include "macros.hpp"
#include "message.hpp"
#include "proof.hpp"

#include <algorithm>

namespace CaDiCaL {

void Internal::watch_clause (Clause * c) {
  const int size = c->size;
  int l0 = c->literals[0], l1 = c->literals[1];
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
// 'resolved' time stamp.  This makes memory allocation and deallocation a
// little bit tricky but saves space and time.  Since the embedding of the
// literals is really important and on the same level of complexity we keep
// both optimizations.

Clause * Internal::new_clause (bool red, int glue) {
  if (glue > MAX_GLUE) glue = MAX_GLUE;
  assert (clause.size () <= (size_t) INT_MAX);
  const int size = (int) clause.size ();  assert (size >= 2);
  size_t bytes = bytes_clause (size);
  bool extended = (red && size > opts.keepsize && glue >= opts.keepglue);
  if (!extended) bytes -= EXTENDED_OFFSET;
  char * ptr = new char[bytes];
  inc_bytes (bytes);
  if (!extended) ptr -= EXTENDED_OFFSET;
  Clause * res = (Clause*) ptr;
  res->extended = extended;
  res->redundant = red;
  res->garbage = false;
  res->reason = false;
  res->moved = false;
  res->glue = glue;
  res->size = size;
  for (int i = 0; i < size; i++) res->literals[i] = clause[i];
  if (extended) res->resolved () = ++stats.resolved;
  clauses.push_back (res);
  if (red) stats.redundant++; else stats.irredundant++;
  LOG (res, "new");
  return res;
}

size_t Internal::delete_clause (Clause * c) {
  LOG (c, "delete");
  if (c->redundant) assert (stats.redundant),   stats.redundant--;
  else              assert (stats.irredundant), stats.irredundant--;
  stats.reduced++;
  size_t bytes = c->bytes ();
  stats.collected += bytes;
  if (proof) proof->trace_delete_clause (c);
  dec_bytes (bytes);
  if (!arena.contains (c->start ())) delete [] c->start ();
  return bytes;
}

// Place literals over the same variable close to each other.  This allows
// eager removal of identical literals and detection of tautological clauses.

struct lit_less_than {
  bool operator () (int a, int b) {
    int s = abs (a), t = abs (b);
    return s < t || (s == t && a < b);
  }
};

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
    if (!tmp) assign (unit);
    else if (tmp < 0) {
      if (!unsat) {
        MSG ("parsed clashing unit");
        clashing_unit = true;
      } else LOG ("original clashing unit produces another inconsistency");
    } else LOG ("original redundant unit");
  } else watch_clause (new_clause (false));
}

Clause * Internal::new_learned_clause (int glue) {
  Clause * res = new_clause (true, glue);
  if (proof) proof->trace_add_clause (res);
  watch_clause (res);
  return res;
}

};
