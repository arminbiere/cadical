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
  return g;
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

int Closure::find_representative(int lit) const {
  int res = lit;
  int nxt;
  do {
    res = nxt;
    nxt = this->representative[nxt];
  } while (nxt != res);
  return res;
}

bool Closure::learn_congruence_unit(int lit) {
  const int val_lit = internal->val(lit);
  if (lit > 0)
    return true;
  if (lit < 0) {
    internal->unsat = true;
    return false;
  }

  internal->assign_unit (lit);
  int conflict = internal->propagate ();

  return !conflict;
}

bool Closure::merge_literals (Closure &closure, int lit, int other) {
  int repr_lit = find_representative(lit);
  int repr_other = find_representative(other);

  if (repr_lit == repr_other) {
    LOG ("already merged %d and %d", lit, other);
    return false;
  }

  const int val_lit = internal->val(lit);
  const int val_other = internal->val(other);

  if (val_lit) {
    if (val_lit == val_other) {
      LOG ("not merging lits %d and %d assigned to same value", lit, other);
      return false;
    }
    if (val_lit == val_other) {
      LOG ("merging lits %d and %d assigned to inconsistent value", lit, other);
      internal->unsat = true;
      internal->learn_empty_clause();
      return false;
    }

    assert (!val_other);
    LOG ("merging assigned %d and unassigned %d", lit, other);
    const unsigned unit = (val_lit < 0) ? -other : other;
    
  }

  if (!val_lit && val_other) {
    LOG ("merging assigned %d and unassigned %d", lit, other);
    const unsigned unit = (val_other < 0) ? -lit : lit;
    learn_congruence_unit(unit);
    return false;
  }

  int smaller = repr_lit;
  int larger = repr_other;

  if (smaller > larger)
    std::swap (smaller, larger);

  assert (find_representative(smaller) == smaller);
  assert (find_representative(larger) == larger);

  if (repr_lit == -repr_other) {
    LOG ("merging clashing %d and %d", lit, other);
    internal->assign_unit (smaller);
    internal->unsat = true;
    return false;
  }

  LOG ("merging %d and %d", lit, other);
  // need i2u or something
  representative[lit] = smaller;
  return false;
}


void Closure::extract_and_gates_with_base_clause (Clause *c) const {
  const std::vector<Clause *> &binaries = this->binaries;
  int size = 0;
  const unsigned arity_limit = min (5, MAX_ARITY); // TODO much larger in kissat
  const unsigned size_limit = arity_limit + 1;
  int64_t max_negbincount = 0;
  internal->clause.clear ();

  for (int lit : *c) {
    signed char v = internal->val (lit);
    if (v < 0)
      continue;
    if (v > 0) {
      assert (!internal->level);
      LOG (c, "found satisfied clause");
     internal->mark_garbage (c);
    }
    if (++size > size_limit) {
      LOG (c, "clause is actually too large, thus skipping");
      return;
    }
    const int64_t count = internal->noccs (-lit);
    if (!count) {
      LOG (c, "%d negated does not occur in any binary clause, thus skipping");
      return;
    }

    if (count > max_negbincount)
      max_negbincount = count;
    internal->clause.push_back(lit);
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
  const size_t clause_size = internal->clause.size();
  for (int i = 0; i < clause_size; ++i) {
    const int lit = internal->clause[i];
    const unsigned count = internal->noccs (-lit);
    internal->mark67 (lit);
    internal->analyzed.push_back (lit);
    if (count < arity) {
      if (reduced < i) {
	internal->clause[i] = internal->clause[reduced];
	internal->clause[reduced++] = lit;
      } else if (reduced == i)
	++reduced;
    }
  }
  const size_t reduced_size = clause_size - reduced;

  
  for (int i = 0; i < clause_size; ++i) {
    if (internal->unsat)
      break;
    if (c->garbage)
      break;
    const int lhs = internal->clause[i];
    const int not_lhs = -lhs;
    for (auto rhs : internal->clause) {
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