#include "solver.hpp"

#include <algorithm>

namespace CaDiCaL {

size_t Solver::bytes_clause (int size) {
  return sizeof (Clause) + (size - 2) * sizeof (int);
}

Clause * Solver::new_clause (bool red, int glue) {
  assert (clause.size () <= (size_t) INT_MAX);
  const int size = (int) clause.size ();  assert (size >= 2);
  size_t bytes = bytes_clause (size);
  Clause * res = (Clause*) new char[bytes];
  inc_bytes (bytes);
  res->resolved = ++stats.resolved;
  res->redundant = red;
  res->garbage = false;
  res->reason = false;
  res->glue = glue;
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

size_t Solver::delete_clause (Clause * c) {
  if (c->redundant)
       assert (stats.clauses.redundant),   stats.clauses.redundant--;
  else assert (stats.clauses.irredundant), stats.clauses.irredundant--;
  assert (stats.clauses.current);
  stats.clauses.current--;
  stats.reduce.clauses++;
  size_t bytes = bytes_clause (c->size);
  stats.reduce.bytes += bytes;
  if (proof) proof->trace_delete_clause (c);
  dec_bytes (bytes);
  LOG (c, "delete");
  delete [] (char*) c;
  return bytes;
}

struct lit_less_than {
  bool operator () (int a, int b) {
    int s = abs (a), t = abs (b);
    return s < t || (s == t && a < b);
  }
};

bool Solver::tautological_clause () {
  sort (clause.begin (), clause.end (), lit_less_than ());
  size_t j = 0;
  int prev = 0;
  for (size_t i = 0; i < clause.size (); i++) {
    int lit = clause[i];
    if (lit == -prev) return true;
    if (lit !=  prev) clause[j++] = lit;
  }
  if (j < clause.size ()) {
    clause.resize (j);
    LOG ("removed %d duplicates", clause.size () - j);
  }
  return false;
}

void Solver::add_new_original_clause () {
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

Clause * Solver::new_learned_clause (int glue) {
  Clause * res = new_clause (true, glue);
  if (proof) proof->trace_add_clause (res);
  watch_clause (res);
  return res;
}

};
