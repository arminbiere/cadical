#include "internal.hpp"

#include <algorithm>

namespace CaDiCaL {

void Internal::watch_clause (Clause * c) {
  assert (c->size > 1);
  int l0 = c->literals[0], l1 = c->literals[1];
  watch_literal (l0, l1, c);
  watch_literal (l1, l0, c);
}

// Since the literals are embedded a clause actually contains always 'size'
// literals and 'literals[2]' should be regarded as 'literals[size]'.
// Clauses have at least 2 literals.  Empty and unit clauses are implicitly
// handled and never allocated.

size_t Internal::bytes_clause (int size) {
  return sizeof (Clause) + (size - 2) * sizeof (int);
}

// Redundant clauses of large glue and large size are extended to hold a
// 'resolved' time stamp.  This makes memory allocation and deallocation a
// little bit tricky but some space and time.  Since the embedding of the
// literals is actually important and on the same level of complexity we
// keep both optimizations.

Clause * Internal::new_clause (bool red, int glue) {
  assert (clause.size () <= (size_t) INT_MAX);
  const int size = (int) clause.size ();  assert (size >= 2);
  size_t bytes = bytes_clause (size);
  bool extended = (red && size > opts.keepsize && glue >= opts.keepglue);
  if (!extended) bytes -= EXTENDED_OFFSET;
  char * ptr = new char[bytes];
  if (!extended) ptr -= EXTENDED_OFFSET;
  Clause * res = (Clause*) ptr;
  inc_bytes (bytes);
  if ((res->extended = extended)) res->resolved () = ++stats.resolved;
  res->redundant = red;
  res->garbage = false;
  res->reason = false;
  res->glue = min (glue, MAX_GLUE);     // restrict to bit-field width
  res->size = size;
  for (int i = 0; i < size; i++) res->literals[i] = clause[i];
  clauses.push_back (res);
  if (red) stats.clauses.redundant++;
  else     stats.clauses.irredundant++;
  if (++stats.clauses.current > stats.clauses.max)
    stats.clauses.max = stats.clauses.current;
  LOG (res, "new");
  return res;
}

size_t Internal::delete_clause (Clause * c) {
  if (c->redundant)
       assert (stats.clauses.redundant),   stats.clauses.redundant--;
  else assert (stats.clauses.irredundant), stats.clauses.irredundant--;
  assert (stats.clauses.current);
  stats.clauses.current--;
  stats.reduce.clauses++;
  size_t bytes = bytes_clause (c->size);
  char * ptr = (char*) c;
  if (!c->extended) bytes -= EXTENDED_OFFSET, ptr += EXTENDED_OFFSET;
  stats.reduce.bytes += bytes;
  if (proof) proof->trace_delete_clause (c);
  dec_bytes (bytes);
  LOG (c, "delete");
  delete [] (char*) ptr;
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
  size_t j = 0;
  int prev = 0;
  for (size_t i = 0; i < clause.size (); i++) {
    int lit = clause[i];
    if (lit == -prev) return true;
    if (lit !=  prev) clause[j++] = prev = lit;
  }
  if (j < clause.size ()) {
    clause.resize (j);
    LOG ("removed %d duplicates", clause.size () - j);
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
