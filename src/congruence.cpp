#include "congruence.hpp"
#include "internal.hpp"

namespace CaDiCaL {
void init_closure (Closure &closure) {}

Gate *Closure::find_and_lits (unsigned arity, unsigned) {
  unsigned hash = hash_lits (this->rhs);
  Gate *g = new Gate;
  g->tag = Gate_Type::And_Gate;
  g->arity = arity;
  g->rhs = {this->rhs};
  auto h = table.find(g);

  if (h != table.end()) {
    delete g;
    return *h;
  }

  else {
    table.insert (g);
    return g;
  }
}

void Internal::init_and_gate_extraction (Closure &closure) {
  std::vector<Clause *> &binaries = closure.binaries;
  for (Clause *c : binaries) {
    assert (c->size == 2);
    const int lit = c->literals[0];
    const int other = c->literals[1];
    noccs (lit)++;
    noccs (other)++;
    occs (lit).push_back (c);
    occs (other).push_back (c);
  }
}


Gate *Closure::new_and_gate (int lhs) {
  assert (rhs.empty()); // or clear like in kissat?
  auto &lits = this->lits;

  for (auto lit : lits) {
    if (lhs != lit) {
      assert (lhs != -lit);
      rhs.push_back(-lit);
    }
  }
  const unsigned arity = rhs.size();
  assert (arity + 1 == lits.size());
  Gate *g = find_and_lits (arity, 0);
  return nullptr;
}

Gate* Internal::find_first_and_gate (const Closure &closure, int lhs) {
  const int not_lhs = -lhs;
  LOG ("trying to find AND gate with first LHS %d", (lhs));
  LOG ("negated LHS %d occurs in %zu binary clauses", (not_lhs), occs (not_lhs));
  unsigned matched = 0;

  const size_t arity = clause.size() - 1;

  for (auto c : occs (not_lhs)) {
    assert (c->size == 2);
    assert (c->literals[0] == lhs || c->literals[1] == lhs);
    const int other = c->literals[0] ^ c->literals[1] ^ not_lhs;
    if (marked67 (other)) {
      ++matched;
      assert (!getbit (other, 2));
      setbit (other, 2);
      analyzed.push_back(other);
    }
  }
  if (matched < arity)
    return nullptr;

  // TODO  
  return nullptr; 
}
 

void Internal::extract_and_gates_with_base_clause (const Closure &closure, Clause *c) {
  std::vector<Clause *> &binaries = closure.binaries;
  int size = 0;
  const unsigned arity_limit = min (5, MAX_ARITY); // TODO much larger in kissat
  const unsigned size_limit = arity_limit + 1;
  int64_t max_negbincount = 0;
  clause.clear ();

  for (int lit : *c) {
    signed char v = val (lit);
    if (v < 0)
      continue;
    if (v > 0) {
      assert (!level);
      LOG (c, "found satisfied clause");
      mark_garbage (c);
    }
    if (++size > size_limit) {
      LOG (c, "clause is actually too large, thus skipping");
      return;
    }
    const int64_t count = noccs (-lit);
    if (!count) {
      LOG (c, "%d negated does not occur in any binary clause, thus skipping");
      return;
    }

    if (count > max_negbincount)
      max_negbincount = count;
    clause.push_back(lit);
  }

  if (size < 3) {
    LOG (c, "is actually too small, thus skipping");
    return;
  }
  
  const size_t arity = size - 1;
  if (max_negbincount < arity) {
    LOG (c, "all literals have less than %u negated occurrences"
            "thus skipping",
            arity);
    return;
  }

  int reduced = 0;
  const size_t clause_size = clause.size();
  for (int i = 0; i < clause_size; ++i) {
    const int lit = clause[i];
    const unsigned count = noccs (-lit);
    mark67 (lit);
    analyzed.push_back (lit);
    if (count < arity) {
      if (reduced < i) {
	clause[i] = clause[reduced];
	clause[reduced++] = lit;
      } else if (reduced == i)
	++reduced;
    }
  }
  const size_t reduced_size = clause_size - reduced;

  
  for (int i = 0; i < clause_size; ++i) {
    if (unsat)
      break;
    if (c->garbage)
      break;
    const int lhs = clause[i];
    const int not_lhs = -lhs;
    for (auto rhs : clause) {
      if (lhs == rhs)
	continue;
     
      
    }
  }
}

void Internal::extract_and_gates (Closure &closure) {
  init_and_gate_extraction (closure);

  for (auto c : clauses) {
    if (c->garbage)
      continue;
    if (c->hyper)
      continue;
    if (c->redundant)
      continue;
    extract_and_gates_with_base_clause(closure, c);
  }
}

void Internal::extract_gates () {
  if (unsat)
    return;
  if (level)
    backtrack ();
  if (!propagate ()) {
    learn_empty_clause ();
    return;
  }

  reset_watches (); // saves lots of memory
  Closure closure (this);
  init_occs();

  extract_and_gates (closure);

  init_watches ();
  connect_watches ();
}
  
}