#include "congruence.hpp"
#include "internal.hpp"

namespace CaDiCaL {

signed char &Closure::marked (int lit){
  return marks[internal->vlit (lit)];
}
void Closure::init_closure () {
  representative.resize(internal->max_var+1);
  for (int i = 0; i < representative.size(); ++i)
    representative[i] = i;
}

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
    LOG (this->rhs, "gate not found in table");
    return nullptr;
  }
}

void Closure::init_and_gate_extraction () {
  LOG ("[gate-extraction]");
  std::vector<Clause *> &binaries = this->binaries;
  for (Clause *c : internal->clauses) {
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    if (c->size > 2)
      continue;
    assert (c->size == 2);
    const int lit = c->literals[0];
    const int other = c->literals[1];
    internal->noccs (lit)++;
    internal->noccs (other)++;
    internal->occs (lit).push_back (c);
    internal->occs (other).push_back (c);
  }
}


Gate *Closure::new_and_gate (int lhs) {
  rhs.clear(); // or clear like in kissat?
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
  if (g) {
    if (merge_literals(g->lhs, lhs)) {
      LOG ("found merged literals");
    }
  } else {
    g = new Gate;
    LOG ("setting %d as lhs", lhs);
    g->lhs = lhs;
    g->tag = Gate_Type::And_Gate;
    g->arity = arity;
    g->rhs = {rhs};
    g->garbage = false;
    g->indexed = true;
    LOG (g->rhs, "inserting in table (%d)", table.size());
    for (const auto it : table) {
      LOG (it->rhs, "found in table");
    }
    table.insert(g);
    

  }
  return g;
}

Gate* Closure::find_first_and_gate (int lhs) {
  assert (internal->analyzed.empty());
  const int not_lhs = -lhs;
  LOG ("trying to find AND gate with first LHS %d", (lhs));
  LOG ("negated LHS %d occurs in %zd binary clauses", (not_lhs), internal->occs (not_lhs).size());
  unsigned matched = 0;

  const size_t arity = lits.size() - 1;

  for (auto c : internal->occs (not_lhs)) {
    LOG (c, "checking clause for candidates");
    assert (c->size == 2);
    assert (c->literals[0] == -lhs || c->literals[1] == -lhs);
    const int other = c->literals[0] ^ c->literals[1] ^ not_lhs;
    signed char &mark = marked (other);
    if (mark) {
      LOG ("marking %d mu2", other);
      ++matched;
      assert (~ (mark & 2));
      mark |= 2;
      internal->analyzed.push_back(other);
    }
  }
  
  LOG ("found %zd initial LHS candidates", internal->analyzed.size());
  if (matched < arity)
    return nullptr;

  return new_and_gate(lhs); 
}

int Closure::find_representative(int lit) const {
  int res = lit;
  int nxt = lit;
  do {
    assert (nxt < representative.size());
    res = nxt;
    nxt = representative[nxt];
  } while (nxt != res);
  return res;
}


void Closure::add_binary_clause (int a, int b) {
  if (internal->unsat)
    return;
  if (a == -b)
    return;
  const signed char a_value = internal->val (a);
  const signed char b_value = internal->val (b);
  if (b > 0)
    return;
  int unit = 0;
  if (a == b)
    unit = a;
  else if (a_value < 0 && !b_value) {
    unit = b;
  } else if (!a_value && b_value < 0)
    unit = a;
  if (unit != 0) {
    learn_congruence_unit(unit);
    return;
  }
  assert (!a_value), assert (!b_value);
  assert (internal->clause.empty());
  internal->clause.push_back(a);
  internal->clause.push_back(b);
  internal->new_hyper_ternary_resolved_clause(false);
  internal->clause.clear();
  
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

bool Closure::merge_literals (int lit, int other) {
  LOG ("merging literals %d and %d", lit, other);
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
  add_binary_clause (-lit, other);
  add_binary_clause (lit, -other);
  // TODO propagate gates
  
  // need i2u or something
  representative[lit] = smaller;
  return false;
}

Gate *Closure::find_remaining_and_gate (int lhs) {
  const unsigned not_lhs = -lhs;

  if (marked (not_lhs) < 2) {
    LOG ("skipping no-candidate LHS %d (%d)", lhs, marked (not_lhs));
    return nullptr;
  }

  LOG ("trying to find AND gate with remaining LHS %d",  (lhs));
  LOG ("negated LHS %d occurs times in %zd binary clauses", (not_lhs),
       internal->noccs(-lhs));

  const unsigned arity = lits.size() - 1;
  unsigned matched = 0;
  assert (1 < arity);

  for (Clause *c : internal->occs (not_lhs) ) {
    assert (c->size == 2);
    assert (c->literals[0] == not_lhs || c->literals[1] == not_lhs);
    const int other = c->literals[0] ^ c->literals[1] ^ not_lhs;
    signed char &mark = marked(other);
    if (mark < 0)
      continue;
    ++matched;
    if (!(mark & 2))
      continue;
    LOG ("marking %d mu3", other);
    assert (!(mark & 4));
    mark |= 4;
  }

  {
    auto q = std::begin(internal->analyzed);
    for (auto lit : internal->analyzed) {
      signed char&mark = marked (lit);
      assert (marked (not_lhs) == 3);
      if (lit == not_lhs) {
	mark = 1;
        continue;
      }

      assert ((mark & 3) == 3);
      if (mark & 4) {
	mark = 4;
	*q = lit;
	++q;
	LOG ("keeping LHS candidate %d", -lit);
      } else {
	LOG ("dropping LHS candidate %d", -lit);
	mark = 1;
      }
      // marks[lit] = mark;

    }
    assert (q != std::end(internal->analyzed));
    assert (marked (not_lhs) == 1);
    internal->analyzed.resize(q - std::begin(internal->analyzed));
    LOG ("after filtering %zu LHS candidate remain", internal->analyzed.size());
  }
  
  if (matched < arity)
    return 0;

  return new_and_gate (lhs);

}

void Closure::extract_and_gates_with_base_clause (Clause *c) {
  assert (!c->garbage);
  LOG(c, "extracting and gates with clause");
  int size = 0;
  const unsigned arity_limit =
      min (5, MAX_ARITY); // TODO much larger in kissat
  const unsigned size_limit = arity_limit + 1;
  int64_t max_negbincount = 0;
  lits.clear ();

  for (int lit : *c) {
    signed char v = internal->val (lit);
    if (v < 0)
      continue;
    if (v > 0) {
      assert (!internal->level);
      LOG (c, "found satisfied clause");
      internal->mark_garbage (c);
      return;
    }
    if (++size > size_limit) {
      LOG (c, "clause is actually too large, thus skipping");
      return;
    }
    const int64_t count = internal->noccs (-lit);
    if (!count) {
      LOG (c,
           "%d negated does not occur in any binary clause, thus skipping %d",
	   lit);
      return;
    }

    if (count > max_negbincount)
      max_negbincount = count;
    lits.push_back (lit);
  }

  if (size < 3) {
    LOG (c, "is actually too small, thus skipping");
    return;
  }

  const size_t arity = size - 1;
  if (max_negbincount < arity) {
    LOG (c,
         "all literals have less than %u negated occurrences"
         "thus skipping",
         arity);
    return;
  }

  internal->analyzed.clear();
  int reduced = 0;
  const size_t clause_size = lits.size ();
  for (int i = 0; i < clause_size; ++i) {
    const int lit = lits[i];
    const unsigned count = internal->noccs (-lit);
    LOG ("marking %d mu1", -lit);
    marked (-lit) = 1;
//    internal->analyzed.push_back (lit);
    if (count < arity) {
      if (reduced < i) {
        lits[i] = lits[reduced];
        lits[reduced++] = lit;
      } else if (reduced == i)
        ++reduced;
    }
  }
  const size_t reduced_size = clause_size - reduced;
  assert (reduced_size);
  LOG (c, "trying as base arity %u AND gate", arity);
  sort (begin (lits), end (lits),
        [this] (int litA, int litB) {
          return (internal->noccs (-litA) < internal->noccs (-litB) ||
		  (internal->noccs (-litA) == internal->noccs (-litB) && litA < litB));
        });

  bool first = true;
  unsigned extracted = 0;

  for (int i = 0; i < clause_size; ++i) {
    if (internal->unsat)
      break;
    if (c->garbage)
      break;
    const int lhs = lits[i];
    LOG ("trying LHS candidate literal %d with %d negated occurrences",
         (lhs), internal->noccs (-lhs));

    if (first) {
      first = false;
      assert (internal->analyzed.empty ());
      if (find_first_and_gate (lhs) != nullptr) {
        ++extracted;
      }
    } else if (internal->analyzed.empty ()) {
        LOG ("early abort AND gate search");
        break;
    } else if (find_remaining_and_gate (lhs)) {
      extracted++;
    }
  }
  
  LOG ("unmarking");
  for (auto lit : lits) {
    marked (-lit) = 0;
  }

  // TODO why do we need this?
  for (auto lit : internal->analyzed) {
    marked (lit) = 0;
  }
  for (auto var: internal->vars) {
    assert (!internal->marked (var));
    assert (!internal->marked (-var));
  }
  internal->analyzed.clear();
  if (extracted)
    LOG (c, "extracted %u with arity %u AND base", extracted, arity);
}

void Closure::extract_and_gates () {


  for (auto var: internal->vars) {
    assert (!internal->marked67 (var));
    assert (!internal->marked67 (-var));
    assert (!internal->marked (var));
    assert (!internal->marked (-var));
  }
  marks.resize (internal->max_var * 2 + 1);
  init_and_gate_extraction ();

  for (auto c : internal->clauses) {
    if (c->garbage)
      continue;
    if (c->size == 2)
      continue;
    if (c->hyper)
      continue;
    if (c->redundant)
      continue;
    extract_and_gates_with_base_clause(c);
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
  init_noccs();

  closure.init_closure();
  closure.extract_and_gates ();

  reset_occs();
  reset_noccs();
  init_watches ();
  connect_watches ();
}
  
}