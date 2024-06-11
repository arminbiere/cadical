#include "congruence.hpp"
#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/
  // marking structure for congruence closure, by reference
signed char &Closure::marked (int lit){
  assert (internal->vlit (lit) < marks.size());
  return marks[internal->vlit (lit)];
}

void Closure::unmark_all () {
  for (auto lit : internal->analyzed) {
    marked (lit) = 0;
  }
  internal->analyzed.clear();
}
void Closure::push_lrat_id (const Clause *const c) {
  if (internal->lrat)
    lrat_chain.push_back(c->id);
}

void Closure::push_lrat_unit (int lit) {
  if (internal->lrat) {
    const unsigned uidx = internal->vlit (-lit);
    uint64_t id = internal->unit_clauses[uidx];
    assert (id);
    lrat_chain.push_back (id);
  }
}

void Closure::mu1(int lit, Clause *c) {
  assert (marked(lit) & 1);
  if (!internal->lrat && false)
    return;
  mu1_ids[internal->vlit (lit)] = c->id;
}

void Closure::mu2(int lit, Clause *c) {
  assert (marked(lit) & 2);
  if (!internal->lrat && false)
    return;
  mu2_ids[internal->vlit (lit)] = c->id;
}

void Closure::mu4(int lit, Clause *c) {
  assert (marked(lit) & 4);
  if (!internal->lrat && false)
    return;
  mu4_ids[internal->vlit (lit)] = c->id;
}

uint64_t Closure::marked_mu1(int lit) {
  return mu1_ids[internal->vlit (lit)];
}

uint64_t Closure::marked_mu2(int lit) {
  return mu2_ids[internal->vlit (lit)];
}

uint64_t Closure::marked_mu4(int lit) {
  return mu4_ids[internal->vlit (lit)];
}
/*------------------------------------------------------------------------*/
int & Closure::representative (int lit) {
  assert (internal->vlit (lit) < representant.size());
  return representant[internal->vlit (lit)];
}
int Closure::representative (int lit) const {
  assert (internal->vlit (lit) < representant.size());
  return representant[internal->vlit (lit)];
}
int Closure::find_representative(int lit) const {
  int res = lit;
  int nxt = lit;
  do {
    res = nxt;
    nxt = representative(nxt);
  } while (nxt != res);
  return res;
}

bool Closure::learn_congruence_unit(int lit) {
  LOG ("adding unit %d with current value %d", lit, internal->val(lit));
  const signed char val_lit = internal->val(lit);
  if (val_lit > 0)
    return true;
  if (val_lit < 0) {
    LOG ("fount unsat");
    internal->unsat = true;
    return false;
  }

  LOG ("assigning");
  internal->assign_unit (lit);
  //assert (internal->watching());
  bool conflict = false; //internal->propagate ();

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

  representative(lit) = smaller;
  ++internal->stats.congruence.congruent;
  return false;
}

/*------------------------------------------------------------------------*/
// Initialization

void Closure::init_closure () {
  representant.resize(2*internal->max_var+3);
  mu1_ids.resize(2*internal->max_var+3);
  mu2_ids.resize(2*internal->max_var+3);
  mu4_ids.resize(2*internal->max_var+3);
  for (auto v : internal->vars) {
    representative(v) = v;
    representative(-v) = -v;
  }
}


void Closure::init_and_gate_extraction () {
  LOG ("[gate-extraction]");
  std::vector<Clause *> &binaries = this->binaries;
  for (Clause *c : internal->clauses) {
    if (c->garbage)
      continue;
    if (c->redundant && c->size != 2)
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


/*------------------------------------------------------------------------*/
// AND gates



// search for the gate in the hash-table. Very simple as we ues the one from the STL
Gate *Closure::find_and_lits (unsigned arity, unsigned) {
  unsigned hash = hash_lits (this->rhs);
  Gate *g = new Gate;
  g->tag = Gate_Type::And_Gate;
  g->arity = arity;
  g->rhs = {this->rhs};
  auto h = table.find(g);

  if (h != table.end()) {
    LOG ((*h)->rhs, "already existing AND gate %d = ", (*h)->lhs);
    delete g;
    return *h;
  }

  else {
    LOG (this->rhs, "gate not found in table");
    return nullptr;
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
    LOG (rhs, "found new gate %d = bigand", lhs);
    g->lhs = lhs;
    g->tag = Gate_Type::And_Gate;
    g->arity = arity;
    g->rhs = {rhs};
    g->garbage = false;
    g->indexed = true;
/*
    LOG (g->rhs, "inserting in table (%d)", table.size());
    for (auto lit : g->rhs) {
      LOG ("mu1 %d %d", lit, marked_mu1(lit));
      LOG ("mu2 %d %d", lit, marked_mu2(lit));
      LOG ("mu4 %d %d", lit, marked_mu4(lit));
      LOG ("mu1 %d %d", -lit, marked_mu1(-lit));
      LOG ("mu2 %d %d", -lit, marked_mu2(-lit));
      LOG ("mu4 %d %d", -lit, marked_mu4(-lit));
    }
    LOG ("mu1 %d %d", lhs, marked_mu1(lhs));
    LOG ("mu1 %d %d", -lhs, marked_mu1(-lhs));
    LOG ("mu2 %d %d", -lhs, marked_mu2(-lhs));
    LOG ("mu4 %d %d", -lhs, marked_mu4(-lhs));
*/
    g->ids.push_back(marked_mu1(-lhs));
    g->ids.push_back(marked_mu2(-lhs));
    g->ids.push_back(marked_mu4(-lhs));
    table.insert(g);
    ++internal->stats.congruence.gates;
    ++internal->stats.congruence.ands;
    

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
      mu2(other, c);
    }
  }
  
  LOG ("found %zd initial LHS candidates", internal->analyzed.size());
  if (matched < arity)
    return nullptr;

  return new_and_gate(lhs); 
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

Gate *Closure::find_remaining_and_gate (int lhs) {
  const int not_lhs = -lhs;

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
    LOG (c, "checking");
    
    assert (c->size == 2);
    assert (c->literals[0] == not_lhs || c->literals[1] == not_lhs);
    const int other = c->literals[0] ^ c->literals[1] ^ not_lhs;
    signed char &mark = marked(other);
    if (!mark)
      continue;
    ++matched;
    mu4_ids[internal->vlit (-lhs)] = c->id;
    if (!(mark & 2))
      continue;
    LOG ("marking %d mu4", other);
    assert (!(mark & 4));
    mark |= 4;
    mu4 (other, c);
  }

  {
    auto q = std::begin(internal->analyzed);
    assert (!internal->analyzed.empty());
    assert (marked (not_lhs) == 3);
    for (auto lit : internal->analyzed) {
      signed char&mark = marked (lit);
      if (lit == not_lhs) {
	mark = 1;
        continue;
      }

      assert ((mark & 3) == 3);
      if (mark & 4) {
	mark = 3;
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
  assert (lrat_chain.empty());
  LOG(c, "extracting and gates with clause");
  int size = 0;
  const unsigned arity_limit =
      min (internal->opts.congruenceandarity, MAX_ARITY); // TODO much larger in kissat
  const unsigned size_limit = arity_limit + 1;
  int64_t max_negbincount = 0;
  lits.clear ();

  for (int lit : *c) {
    signed char v = internal->val (lit);
    if (v < 0) {
      push_lrat_unit(lit);
      continue;
    }
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
    mu1(-lit, c);
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

  for (auto lit : internal->analyzed) {
    marked (lit) = 0;
    assert (!marked (-lit));
  }
  internal->analyzed.clear();
  for (auto var: internal->vars) {
    assert (!marked (var));
    assert (!marked (-var));
  }
  lrat_chain.clear();
  if (extracted)
    LOG (c, "extracted %u with arity %u AND base", extracted, arity);
}

void Closure::extract_and_gates () {
  if (!internal->opts.congruenceand)
    return;
  for (auto var: internal->vars) {
    assert (!internal->marked67 (var));
    assert (!internal->marked67 (-var));
    assert (!internal->marked (var));
    assert (!internal->marked (-var));
  }
  marks.resize (internal->max_var * 2 + 3);
  init_and_gate_extraction ();

  const size_t size = internal->clauses.size();
  for (size_t i = 0; i < size && !internal->terminated_asynchronously (); ++i) { // we can learn new binary clauses, but no for loop
    Clause *c = internal->clauses[i];
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

/*------------------------------------------------------------------------*/
void Closure::find_units () {
  size_t units = 0;
  for (auto v : internal->vars) {
  RESTART:
    if (!internal->flags (v).active ())
      continue;
    for (int sgn = -1; sgn < 1; sgn += 2) {
      int lit = v * sgn;
      for (auto c : internal->occs (lit)) {
        const int other = lit ^ c->literals[0] ^ c->literals[1];
        if (marked (-other)) {
          LOG (c, "binary clause %d %d and %d %d give unit", lit, other,
               lit, -other, lit);
	  ++units;
          bool failed = !learn_congruence_unit (lit);
          unmark_all ();
          if (failed)
            return;
          else
            goto RESTART;
        }
	if (marked(other))
	  continue;
	marked (other) = 1;
	internal->analyzed.push_back(other);
      }
      unmark_all();
    }
    assert (internal->analyzed.empty());
  }
  LOG ("found %zd", units);
}


/*------------------------------------------------------------------------*/
void Closure::extract_gates() {
  extract_and_gates();
  if (internal->unsat)
    return;
  //extract_xor_gates
  if (internal->unsat)
    return;
  //extract_ite_gates
}
/*------------------------------------------------------------------------*/
// top lever function to exctract gate
void Internal::extract_gates () {
  if (unsat)
    return;
  if (!internal->opts.congruence)
    return;
  if (level)
    backtrack ();
  if (!propagate ()) {
    learn_empty_clause ();
    return;
  }

  const int64_t old = stats.congruence.congruent;
  const bool dedup = opts.deduplicate;
  opts.deduplicate = true;
  mark_duplicated_binary_clauses_as_garbage ();
  opts.deduplicate = dedup;
  ++stats.congruence.rounds;
  reset_watches (); // saves lots of memory
  Closure closure (this);
  init_occs();
  init_noccs();

  closure.init_closure();
  closure.extract_gates ();
  if (!internal->unsat) {
    closure.find_units();
  }

  reset_occs();
  reset_noccs();
  init_watches ();
  connect_watches ();
  
  if (!unsat && !propagate())
    unsat = true;

  report('=', !opts.reportall && !(stats.congruence.congruent - old));
}
  
}