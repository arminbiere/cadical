#include "congruence.hpp"
#include "internal.hpp"
#include <iterator>
#include <vector>

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

void Closure::mark_garbage (Gate *g) {
  LOG(g->rhs, "marking as garbage %d", g->lhs);
  assert (!g->garbage);
  g->garbage = true;
  garbage.push_back(g);
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
  assert (lit != -1);
  internal->assign_unit (lit);
  
  LOG ("propagating %d %d", internal->propagated, internal->trail.size());
  bool no_conflict = internal->propagate ();

  if (no_conflict)
    return true;
  internal->learn_empty_clause();

  return false;
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
    swap (smaller, larger);

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

  representative(larger) = smaller;
  representative(-larger) = -smaller;
  schedule_literal(larger);
  ++internal->stats.congruence.congruent;
  return false;
}

/*------------------------------------------------------------------------*/
GOccs &Closure::goccs (int lit) { return gtab[internal->vlit (lit)]; }

void Closure::connect_goccs (Gate *g, int lit) {
  goccs (lit).push_back (g);
}

uint64_t &Closure::largecount (int lit) {
  assert (internal->vlit (lit) < glargecounts.size());
  return glargecounts[internal->vlit (lit)];
}

/*------------------------------------------------------------------------*/
// Initialization

void Closure::init_closure () {
  representant.resize(2*internal->max_var+3);
  marks.resize(2*internal->max_var+3);
  mu1_ids.resize(2*internal->max_var+3);
  mu2_ids.resize(2*internal->max_var+3);
  mu4_ids.resize(2*internal->max_var+3);
  scheduled.resize(internal->max_var+1);
  gtab.resize(2*internal->max_var+3);
  for (auto v : internal->vars) {
    representative(v) = v;
    representative(-v) = -v;
  }
  units = internal->propagated;
}


void Closure::init_and_gate_extraction () {
  LOG ("[gate-extraction]");
  vector<Clause *> &binaries = this->binaries;
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
// Simplification
bool Closure::skip_and_gate(Gate *g) {
  assert (g->tag == Gate_Type::And_Gate);
  if (g->garbage)
    return true;
  const int lhs = g->lhs;
  if (internal->val(lhs) > 0) {
    mark_garbage(g);
    return true;
  }

  assert (g->arity > 1);
  return false;
}

bool Closure::skip_xor_gate(Gate *g) {
  assert (g->tag == Gate_Type::XOr_Gate);
  if (g->garbage)
    return true;
  assert (g->arity > 1);
  return false;
}

void Closure::shrink_and_gate(Gate *g, int falsifies, int clashing) {
  if (falsifies) {
    g->rhs[0] = falsifies;
    g->rhs.resize(1);
  } else if (clashing) {
    g->rhs[0] = clashing;
    g->rhs[1] = -clashing;
    g->rhs.resize(2);
  }
}


void Closure::update_and_gate(Gate *g, GatesTable::iterator it, int falsifies, int clashing) {
  bool garbage = true;
  if (falsifies || clashing) {
    learn_congruence_unit (-g->lhs);
  } else if (g->arity == 1) {
    const signed char v = internal->val (g->lhs);
    if (v > 0)
      learn_congruence_unit (g->rhs[0]);
    else if (v < 0)
      learn_congruence_unit (-g->rhs[0]);
    else if (merge_literals(g->lhs, g->rhs[0])) {
      ++internal->stats.congruence.unaries;
      ++internal->stats.congruence.unary_and;
    } else {
      Gate *h = find_and_lits (g->arity, g->rhs);
      if (h) {
        assert (garbage);
        if (merge_literals (g->lhs, h->lhs))
          ++internal->stats.congruence.ands;
      } else {
        if (g->indexed) {
          LOG (g->rhs, "removing gate from table %d = %s", g->lhs,
               string_of_gate (g->tag).c_str ());
          (void)table.erase (it);
        }

        table.insert (g);
        g->indexed = true;
        garbage = false;
      }
    }
  }
  if (garbage && !internal->unsat)
    mark_garbage(g);
}


  void Closure::update_xor_gate(Gate *g, GatesTable::iterator git) {
  assert (g->tag == Gate_Type::XOr_Gate);
  LOG (g->rhs, "updating gate %d = %s", g->lhs, string_of_gate(g->tag).c_str());
  bool garbage = true;
  if (g->arity == 0)
    learn_congruence_unit (-g->lhs);
  else if (g->arity == 1) {
    const signed char v = internal->val (g->lhs);
    if (v > 0)
      learn_congruence_unit (g->rhs[0]);
    else if (v < 0)
      learn_congruence_unit (-g->rhs[0]);
    else if (merge_literals(g->lhs, g->rhs[0])) {
      ++internal->stats.congruence.unaries;
      ++internal->stats.congruence.unary_and;
    }
  } else {
    Gate *h = find_and_lits (g->arity, g->rhs);
    if (h) {
      assert (garbage);
      if (merge_literals (g->lhs, h->lhs))
        ++internal->stats.congruence.ands;
    } else {
      if (g->indexed) {
	LOG (g->rhs, "removing gate from table %d = %s", g->lhs, string_of_gate(g->tag).c_str());
        table.erase (git);
      }

      table.insert (g);
      g->indexed = true;
      assert (table.find(g) != end (table));
      garbage = false;
    }
  }
  if (garbage && !internal->unsat)
    mark_garbage(g);
}

void Closure::simplify_and_gate (Gate *g) {
  if (skip_and_gate (g))
    return;
  GatesTable::iterator git = (g->indexed ? table.find(g) : end(table));
  LOG (g->rhs, "simplifying gate %d =", g->lhs);
  int falsifies = 0;
  auto it = begin(g->rhs);
  for (auto lit : g->rhs) {
    const signed char v = internal->val (lit);
    if (v > 0)
      continue;
    if (v < 0) {
      falsifies = lit;
      continue;
    }
    *it++ = lit;
  }

  if (end(g->rhs) != it){
    g->shrunken = true;
    g->rhs.resize(end(g->rhs) - it);
    LOG (g->rhs, "shrunken gate %d =", g->lhs);
  }
  shrink_and_gate(g, falsifies);
  update_and_gate(g, git, falsifies);
  ++internal->stats.congruence.simplified_ands;
  ++internal->stats.congruence.simplified;
}


bool Closure::simplify_gate (Gate *g) {
  switch (g->tag) {
  case Gate_Type::And_Gate:
    simplify_and_gate (g);
    break;
  case Gate_Type::XOr_Gate:
    simplify_xor_gate (g);
    break;
  default:
    assert (false);
    break;
  }

  return !internal->unsat;
  
}

bool Closure::simplify_gates (int lit) {
  for (auto g : goccs (lit)) {
    if (!simplify_gate (g))
      return false;
  }
  return true;  
}
/*------------------------------------------------------------------------*/
// AND gates



// search for the gate in the hash-table. Very simple as we ues the one from the STL
Gate *Closure::find_and_lits (int arity, const vector<int> &rhs) {
  Gate *g = new Gate;
  g->tag = Gate_Type::And_Gate;
  g->arity = arity;
  g->rhs = {rhs};
  auto h = table.find(g);

  if (h != table.end()) {
    LOG ((*h)->rhs, "already existing AND gate %d = ", (*h)->lhs);
    delete g;
    return *h;
  }

  else {
    LOG (this->rhs, "gate not found in table");
    delete g;
    return nullptr;
  }
}

Gate *Closure::new_and_gate (int lhs) {
  rhs.clear();
  auto &lits = this->lits;

  for (auto lit : lits) {
    if (lhs != lit) {
      assert (lhs != -lit);
      rhs.push_back(-lit);
    }
  }
  const unsigned arity = rhs.size();
  assert (arity + 1 == lits.size());
  Gate *g = find_and_lits (arity, this->rhs);
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
    g->ids.push_back(marked_mu1(-lhs));
    g->ids.push_back(marked_mu2(-lhs));
    g->ids.push_back(marked_mu4(-lhs));
    table.insert(g);
    ++internal->stats.congruence.gates;
    ++internal->stats.congruence.ands;
    for (auto lit : g->rhs) {
      connect_goccs(g, lit);
    }
    

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
  LOG ("learning clause for equivalence %d %d", a, b);
  if (internal->unsat)
    return;
  if (a == -b)
    return;
  const signed char a_value = internal->val (a);
  const signed char b_value = internal->val (b);
  LOG ("learning clause for equivalence %d %d", a_value, b_value);
  if (b_value > 0)
    return;
  int unit = 0;
  if (a == b)
    unit = a;
  else if (a_value < 0 && !b_value) {
    unit = b;
  } else if (!a_value && b_value < 0)
    unit = a;
  if (unit != 0) {
    LOG ("clause reduced to unit %d", unit);
    learn_congruence_unit(unit);
    return;
  }
  LOG ("learning clause for equivalence");
  assert (!a_value), assert (!b_value);
  assert (internal->clause.empty());
  internal->clause.push_back(a);
  internal->clause.push_back(b);
  Clause *res = internal->new_hyper_ternary_resolved_clause_and_watch (false);
  LOG (res, "learning clause");
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
    auto q = begin(internal->analyzed);
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
    assert (q != end(internal->analyzed));
    assert (marked (not_lhs) == 1);
    internal->analyzed.resize(q - begin(internal->analyzed));
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
      min (internal->opts.congruenceandarity, MAX_ARITY);
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
  for (size_t i = 0; i < clause_size; ++i) {
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

  internal->reset_occs();
  internal->init_occs();
  for (auto v : internal->vars)
    internal->noccs(v) = internal->noccs(-v) = 0;
}

/*------------------------------------------------------------------------*/
// XOR gates

uint64_t &Closure::new_largecounts(int lit) {
  assert (internal->vlit(lit) < gnew_largecounts.size());
  return gnew_largecounts[internal->vlit(lit)];
}

uint64_t &Closure::largecounts(int lit) {
  assert (internal->vlit(lit) < glargecounts.size());
  return glargecounts[internal->vlit(lit)];
}

unsigned parity_lits (vector<int> lits) {
  unsigned res = 0;
  for (auto lit : lits)
    res ^= (lit < 0);
  return res;
}

void inc_lits (vector<int>& lits){
  bool carry = 1;
  for (int i = 0; i < lits.size() && carry; ++i) {
    int lit = lits[i];
    carry = (lit > 0);
    lits[i] = -lit;
  }
}

void Closure::check_ternary (int a, int b, int c) {
  if (!internal->opts.check)
    return;
  auto &clause = internal->clause;
  assert (clause.empty ());
  clause.push_back(a);
  clause.push_back(b);
  clause.push_back(c);
  internal->external->check_learned_clause ();
  clause.clear();
}

void Closure::add_xor_shrinking_proof_chain(Gate const *const g, int pivot) {
  if (!internal->proof)
    return;
  LOG ("starting XOR shrinking proof chain");
  auto &clause = internal->clause;
  assert (clause.empty());

  for (auto lit : g->rhs)
    clause.push_back (lit);

  const int lhs = g->lhs;
  clause.push_back(-lhs);
  const unsigned parity = (lhs > 0);
  assert (parity == parity_lits(clause));
  const size_t size = clause.size();
  const unsigned end = 1u << size;
  for (unsigned i = 0; i != end; ++i) {
    while (i && parity != parity_lits(clause))
      inc_lits(clause);
    clause.push_back(pivot);
    check_and_add_to_proof_chain (clause);
    clause.pop_back();
    clause.push_back(-pivot);
    check_and_add_to_proof_chain (clause);
    clause.pop_back();
    check_and_add_to_proof_chain (clause);
    // TODO missing deletion
    
    inc_lits(clause);
  }
  clause.clear();
}

void Closure::check_xor_gate_implied(Gate const *const g) {
  assert (g->tag == Gate_Type::XOr_Gate);
  if (!internal->opts.check)
    return;
  const int lhs = g->lhs;
  LOG (g->rhs, "checking gate %d = bigxor", g->lhs);
  auto &clause = internal->clause;
  assert (clause.empty());
  for (auto other : g->rhs) {
    assert (other > 0);
    clause.push_back(other);
  }
  const unsigned arity = g->arity;
  const unsigned end = 1u << arity;
  const unsigned parity = (lhs > 0);

  for (unsigned i = 0; i != end; ++i) {
    while (i && parity_lits (clause) != parity)
      inc_lits (clause);
    internal->external->check_learned_clause ();
    inc_lits (clause);
  }
  clause.clear();
}
  
// 
// TODO moreg with find_and_lits
Gate* Closure::find_xor_lits (int arity, const vector<int> &rhs) {
  Gate *g = new Gate;
  g->tag = Gate_Type::XOr_Gate;
  g->arity = arity;
  g->rhs = {rhs};
  auto h = table.find(g);

  if (h != table.end()) {
    LOG ((*h)->rhs, "already existing XOR gate %d = ", (*h)->lhs);
    delete g;
    return *h;
  }

  else {
    LOG (this->rhs, "gate not found in table");
    delete g;
    return nullptr;
  }
}

void Closure::check_and_add_to_proof_chain (vector<int> &clause) {
  internal->external->check_learned_clause ();
  if (internal->proof) {
    vector<uint64_t> lrat_chain;
    const uint64_t id = ++internal->clause_id;
    internal->proof->add_derived_clause (id, true,
                                         internal->clause, lrat_chain);
  }
}
void Closure::simplify_and_add_to_proof_chain (
					       vector<int> &unsimplified, vector<int> &chain) {
  vector<int> &clause = internal->clause;
  assert (clause.empty ());
#ifndef NDEBUG
  for (auto lit : unsimplified) {
    assert (!(marked (lit) & 4));
#endif
  }

  bool trivial = false;
  for (auto lit: unsimplified) {
    signed char &lit_mark = marked(lit);
    if (lit_mark & 4)
      continue;
    signed char &not_lit_mark = marked(-lit);
    if (not_lit_mark & 4) {
      trivial = true;
      break;
    }
    lit_mark |= 4;
    clause.push_back(lit);
  }
  for (auto lit : clause) {
    signed char &mark = marked(lit);
    assert (mark & 4);
    mark &= ~4u;
  }

  if (!trivial) {
    check_and_add_to_proof_chain (clause);
    chain = move (clause);
  }
  clause.clear ();
}

void Closure::add_xor_matching_proof_chain(Gate *g, int lhs1, int lhs2) {
  if (lhs1 == lhs2)
    return;
  if (!internal->proof)
    return;
  const size_t reduced_arity = g->arity - 1;
  unsimplified = g->rhs;
  
  LOG ("starting XOR matching proof");
  do {
    const size_t size = unsimplified.size();
    assert (size < 32);
    for (size_t i = 0; i != 1u << size; ++i) {
      unsimplified.push_back(-lhs1);
      unsimplified.push_back(lhs2);
      simplify_and_add_to_proof_chain (unsimplified, chain);
      unsimplified.resize(unsimplified.size() - 2);
      unsimplified.push_back(lhs1);
      unsimplified.push_back(-lhs2);
      simplify_and_add_to_proof_chain (unsimplified, chain);
      unsimplified.resize(unsimplified.size() - 2);
      inc_lits(unsimplified);
    }
    assert (!unsimplified.empty());
    unsimplified.pop_back();
  } while (!unsimplified.empty());
  LOG ("finished XOR matching proof");
}

Gate *Closure::new_xor_gate (int lhs) {
  rhs.clear();

  for (auto lit : lits) {
    if (lhs != lit && -lhs != lit) {
      assert (lit > 0);
      rhs.push_back(lit);
    }
  }
  const unsigned arity = rhs.size();
  assert (arity + 1 == lits.size());
  Gate *g = find_xor_lits (arity, this->rhs);
  if (g) {
    check_xor_gate_implied (g);
    add_xor_matching_proof_chain(g, g->lhs, lhs);
    if (merge_literals(g->lhs, lhs)) {
      LOG ("found merged literals");
    }
  } else {
    g = new Gate;
    LOG (rhs, "found new gate %d = xor", lhs);
    g->lhs = lhs;
    g->tag = Gate_Type::XOr_Gate;
    g->arity = arity;
    g->rhs = {rhs};
    g->garbage = false;
    g->indexed = true;
    table.insert(g);
    ++internal->stats.congruence.gates;
    ++internal->stats.congruence.xors;
    check_xor_gate_implied (g);
    for (auto lit : g->rhs) {
      connect_goccs(g, lit);
    }
    

  }
  return g;
}

void Closure::init_xor_gate_extraction (std::vector<Clause *> &candidates) {
  const unsigned arity_limit = internal->opts.congruencexorarity;
  const unsigned size_limit = arity_limit + 1;
  glargecounts.resize (2 * internal->vsize, 0);

  for (auto c : internal->clauses) {
    LOG (c, "considering clause for XOR");
    if (c->redundant)
      continue;
    if (c->garbage)
      continue;
    unsigned size = 0;
    for (auto lit : *c) {
      const signed char v = internal->val (lit);
      if (v < 0)
        continue;
      if (v > 0) {
        LOG (c, "satisfied by %d", lit);
        internal->mark_garbage (c);
        goto CONTINUE_COUNTING_NEXT_CLAUSE;
      }
      if (size == size_limit)
        goto CONTINUE_COUNTING_NEXT_CLAUSE;
      ++size;
    }

    if (size < 3)
      continue;
    for (auto lit : *c) {
      if (internal->val (lit))
        continue;
      ++largecounts (lit);
    }

    LOG (c, "considering clause for XOR as candidate");
    candidates.push_back (c);
  CONTINUE_COUNTING_NEXT_CLAUSE:;
  }

  LOG ("considering %d out of %d", candidates.size(), internal->irredundant());
  const unsigned rounds = internal->opts.congruencexorcounts;
  const size_t original_size = candidates.size(); 
  LOG ("resizing glargecounts to size %zd", glargecounts.size ());
  for (unsigned round = 0; round < rounds; ++round) {
    LOG ("round %d of XOR extraction", round);
    size_t removed = 0;
    gnew_largecounts.resize (2 * internal->vsize);
    unsigned cand_size = candidates.size();
    size_t j = 0;
    for (size_t i = 0; i < cand_size; ++i) {
      Clause *c = candidates[i];
      LOG (c, "considering");
      unsigned size = 0;
      for (auto lit: *c) {
        if (!internal->val (lit))
          ++size;
      }
      assert (3 <= size);
      assert (size <= size_limit);
      const unsigned arity = size - 1;
      const unsigned needed_clauses = 1u << (arity - 1);
      for (auto lit : *c) {
        if (largecounts (lit) < needed_clauses) {
	  LOG (c, "not enough occurrences, so ignoring");
          removed++;
          goto CONTINUE_WITH_NEXT_CANDIDATE_CLAUSE;
        }
      }
      for (auto lit : *c)
        if (!internal->val (lit))
	  new_largecounts (lit)++;
      candidates[j++] = candidates[i];

    CONTINUE_WITH_NEXT_CANDIDATE_CLAUSE:;
    }
    candidates.resize(j);
    LOG ("moving counts");
    glargecounts = std::move(gnew_largecounts);
    gnew_largecounts.clear();
    LOG ("moving counts %d", glargecounts.size());
    if (!removed)
      break;

    LOG ("after round %d, %d (%d %%) remain", round, candidates.size(), candidates.size() / (1+original_size )* 100);
  }

  for (auto c : candidates) {
    for (auto lit : *c)
      internal->occs (lit).push_back(c);
  }

  // for (auto lit : internal->lits) {
  //   internal->noccs(lit) = largecount(lit);
  // }
  // glargecounts.clear();
}

Clause *Closure::find_large_xor_side_clause (std::vector<int> &lits) {
  unsigned least_occurring_literal = 0;
  unsigned count_least_occurring = UINT_MAX;
  const size_t size_lits = lits.size();
#if defined(LOGGING) || !defined(NDEBUG)
  const unsigned arity = size_lits - 1;
#endif
#ifndef NDEBUG
  const unsigned count_limit = 1u << (arity - 1);
#endif
  LOG (lits, "trying to find arity %u XOR side clause", arity);
  for (auto lit: lits) {
    assert (!internal->val(lit));
    marked (lit) = 1;
    unsigned count = largecount (lit);
    assert (count_limit <= count);
    if (count >= count_least_occurring)
      continue;
    count_least_occurring = count;
    least_occurring_literal = lit;
  }
  Clause *res = 0;
  assert (least_occurring_literal);
  LOG ("searching XOR side clause watched by %d#%u",
       least_occurring_literal, count_least_occurring);
  LOG ("searching for size %ld", size_lits);
  // TODO this is the wrong thing to iterate on!
  for (auto c : internal->occs (least_occurring_literal)) {
    LOG (c, "checking");
    if (c->size == 2) // TODO kissat has break
      continue;
    if (c->garbage)
      continue;
    if (c->size<size_lits)
      continue;
    size_t found = 0;
    LOG ("detailed look");
    for (auto other : *c) {
      const signed char value = internal->val (other);
      if (value < 0)
        continue;
      if (value > 0) {
        LOG (c, "found satisfied %d in", other);
        internal->mark_garbage (c);
        assert (c->garbage);
        break;
      }
      if (marked(other))
        found++;
      else {
        LOG ("not marked %d", other);
        found = 0;
        break;
      }
    }
    if (found == size_lits && !c->garbage) {
      res = c;
      break;
    } else {
      LOG ("too few literals");
    }
  }
  for (auto lit : lits)
    marked(lit) = 0;
  if (res)
    LOG (res, "found matching XOR side");
  else
    LOG ("no matching XOR side clause found");
  return res;
}

void Closure::extract_xor_gates_with_base_clause (Clause *c) {
  LOG (c, "checking clause");
  lits.clear();
  int smallest = 0;
  int largest = 0;
  const unsigned arity_limit = internal->opts.congruencexorarity;
  const unsigned size_limit = arity_limit + 1;
  unsigned negated = 0, size = 0;
  bool first = true;
  for (auto lit : *c) {
    const signed char v = internal->val (lit);
    if (v < 0)
      continue;
    if (v > 0) {
      internal->mark_garbage(c);
      return;
    }
    if (size == size_limit) {
      LOG (c, "size limit reached");
      return;
    }

    if (first) {
      largest = smallest = lit;
      first = false;
    } else {
      assert (smallest);
      assert (largest);
      if (internal->vlit(lit) < internal->vlit(smallest)) {
	LOG ("new smallest %d", lit);
	smallest = lit;
      }
      if (internal->vlit(lit) > internal->vlit (largest)) {
	if (largest < 0) {
	  LOG (c, "not largest %d (largest: %d) occurs negated in XOR base", lit, largest);
	  return;
	}
	largest = lit;
      }
    }
    if (lit < 0 && internal->vlit(lit) < internal->vlit(largest)) {
      LOG (c, "negated literal %d not largest in XOR base", lit);
      return;
    }
    if (lit < 0 && negated++) {
      LOG (c, "more than one negated literal in XOR base");
      return;
    }
    lits.push_back(lit);
    ++size;
  }
  assert (size == lits.size());
  if (size < 3) {
    LOG (c, "short XOR base clause");
    return;
  }

  LOG ("double checking if possible");
  const unsigned arity = size - 1;
  const unsigned needed_clauses = 1u << (arity - 1);
  for (auto lit : lits) {
    for (int sign = 0; sign != 2; ++sign, lit = -lit) {
      unsigned count = largecount(lit);
      if (count >= needed_clauses)
	continue;
      LOG (c, "literal %d in XOR base clause only occurs %u times in large clause thus skipping",
	   lit, count);
      return;
    }
  }

  LOG ("checking for XOR side clauses");
  assert (smallest && largest);
  const unsigned end = 1u << arity;
  assert (negated == parity_lits(lits));
  unsigned found = 0;
  for (unsigned i = 0; i != end; ++i) {
    while (i && parity_lits(lits) != negated)
      inc_lits (lits);
    if (i) {
      Clause *d = find_large_xor_side_clause (lits);
      if (!d)
	return;
      assert (!d->redundant);
    } else
      assert (!c->redundant);
    inc_lits (lits);
    ++found;
  }
  
  while (parity_lits (lits) != negated)
    inc_lits (lits);
  LOG (lits, "found all needed %u matching clauses:", found);
  assert (found == 1u << arity);
  if (negated) {
    auto p = begin(lits);
    int lit;
    while ((lit = *p) > 0)
      p++;
    LOG ("flipping RHS literal %d", (lit));
    *p = - lit;
  }
  LOG (lits, "normalized negations");
  unsigned extracted = 0;
  for (auto lhs: lits) {
    if (!negated)
      lhs = -lhs;
    Gate *g = new_xor_gate (lhs);
    if (g)
      extracted++;
    if (internal->unsat)
      break;
  }
  if (!extracted)
    LOG ("no arity %u XOR gate extracted", arity);
}
void Closure::extract_xor_gates () {
  if (!internal->opts.congruencexor)
    return;
  LOG ("starting extracting XOR");
  std::vector<Clause *> candidates = {};
  init_xor_gate_extraction(candidates);
  for (auto c : candidates) {
    if (internal->unsat)
      break;
    if (c->garbage)
      continue;
    extract_xor_gates_with_base_clause (c);
  }
  // reset_xor_gate_extraction();
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
	if (c->size != 2)
	  continue;
        const int other = lit ^ c->literals[0] ^ c->literals[1];
        if (marked (-other)) {
          LOG (c, "binary clause %d %d and %d %d give unit %d", lit, other,
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
  LOG ("found %zd units", units);
}

void Closure::find_equivalences () {
  assert (!internal->unsat);

  for (auto v : internal->vars) {
  RESTART:
    if (!internal->flags (v).active ())
      continue;
    int lit = v;
    for (auto c : internal->occs (lit)) {
      if (c->size != 2)
	continue;
      assert (c->size == 2);
      const int other = lit ^ c->literals[0] ^ c->literals[1];
      if (abs(lit) > abs(other))
	continue;
      if (marked (other))
	continue;
      internal->analyzed.push_back(other);
      marked (other) = true;
    }

    if (internal->analyzed.empty())
      continue;
    
    for (auto c : internal->occs (-lit)) {
      assert (c->size == 2);
      assert (c->literals[0] == -lit || c->literals[1] == -lit);
      const int other = (-lit) ^ c->literals[0] ^ c->literals[1];
      if (abs(-lit) > abs(other))
	continue;
      if (lit == other)
	continue;
      if (marked (-other)) {
	int lit_repr = find_representative(lit);
	int other_repr = find_representative(other);
	LOG ("%d and %d are the representative", lit_repr, other_repr);
	if (lit_repr != other_repr) {
	  if (merge_literals(lit_repr, other_repr)) {
	    COVER (true);
	    ++internal->stats.congruence.congruent;
	  }
	  unmark_all();
	  if (internal->unsat)
	    return;
	  else
	    goto RESTART;
	}
      }
    }
    unmark_all();
  }
  assert (internal->analyzed.empty());
  LOG ("found %zd equivalences", schedule.size());
}

/*------------------------------------------------------------------------*/

bool gate_contains(Gate *g, int lit) {
  return find (begin(g->rhs), end (g->rhs), lit) != end (g->rhs);
}

void Closure::rewrite_and_gate (Gate *g, int dst, int src) {
  if (skip_and_gate(g))
    return;
  if (!gate_contains (g, src))
    return;
  assert (src);
  assert (dst);
  assert (internal->val (src) == internal->val (dst));
  GatesTable::iterator git = (g->indexed ? table.find(g) : end(table));
  LOG (g->rhs, "rewriting %d into %d in %d = bigand", src, dst, g->lhs);
  int clashing = 0, falsifies = 0;
  unsigned dst_count = 0, not_dst_count = 0;
  auto q = begin(g->rhs);
  for (int &lit: g->rhs) {
    if (lit == src)
      lit = dst;
    if (lit == -g->lhs) {
      LOG ("found negated LHS literal %d", lit);
      clashing = lit;
      break;
    }
    const signed char val = internal->val (lit);
    if (val > 0)
      continue;
    if (val < 0) {
      LOG ("found falsifying literal %d", (lit));
      falsifies = lit;
      break;
    }
    if (lit == dst) {
      if (not_dst_count) {
        LOG ("clashing literals %d and %d", (-dst), (dst));
        clashing = -dst;
        break;
      }
      if (dst_count++)
        continue;
    }
    if (lit == -dst) {
      if (dst_count) {
        assert (!not_dst_count);
        LOG ("clashing literals %d and %d", (dst),  (-dst));
        clashing = dst;
        break;
      }
      assert (!not_dst_count);
      ++not_dst_count;
    }
    *q++ = lit;
  }

  assert (dst_count <= 2);
  assert (not_dst_count <= 1);
  shrink_and_gate(g, falsifies, clashing);
  LOG (g->rhs, "rewriten g as %d = bigand", g->lhs);
  update_and_gate(g, git, falsifies, clashing);
}

bool Closure::rewrite_gate (Gate *g, int dst, int src) {
  switch (g->tag) {
  case Gate_Type::And_Gate:
    rewrite_and_gate (g, dst, src);
    break;
  case Gate_Type::XOr_Gate:
    rewrite_xor_gate (g, dst, src);
    break;
  default:
    assert (false);
    break;
  }
  return !internal->unsat;
}
bool Closure::rewrite_gates(int dst, int src) {
  for (auto g : goccs (src)) {
    if (!rewrite_gate (g, dst, src))
      return false;
    else if (!g->garbage && gate_contains (g, dst))
      goccs (dst).push_back(g);
  }
  goccs (src).clear();
  return true;
}

bool Closure::rewriting_lhs (Gate *g, int dst) {
  if (dst != g->lhs && dst != -g->lhs)
    return false;
  mark_garbage (g);
  return true;
}

void Closure::rewrite_xor_gate (Gate *g, int dst, int src) {
  LOG (g->rhs, "rewriting %d = XOR", g->lhs);
  if (skip_xor_gate (g))
    return;
  if (rewriting_lhs (g, dst))
    return;
  if (!gate_contains (g, src))
    return;
  LOG (g->rhs, "simplifying (%d -> %d) %d = bigxor", src, dst, g->lhs);
  GatesTable::iterator git = (g->indexed ? table.find(g) : end(table));
  size_t j = 0, dst_count = 0;
  unsigned original_dst_negated = (dst < 0);
  dst = abs (dst);
  unsigned negate = original_dst_negated;
  const size_t size = g->rhs.size ();
  for (size_t i = 0; i < size; ++i) {
    int lit = g->rhs[i];
    assert (lit > 0);
    if (lit == src)
      lit = dst;
    const signed char v = internal->val (lit);
    if (v > 0)
      negate ^= 1;
    if (v)
      continue;
    if (lit == dst)
      dst_count++;
    g->rhs[j++] = lit;
  }
  if (negate) {
    LOG ("flipping LHS");
    g->lhs = -g->lhs;
  }
  assert (dst_count <= 2);
  if (dst_count == 2) {
    j = 0;
    for (auto i = 0; i < g->rhs.size(); ++i) {
      const int lit = g->rhs[i];
      if (lit != dst)
	g->rhs[j++] = g->rhs[i];
    }
    assert (j == g->rhs.size() - 2);
    g->rhs.resize(j);
    g->shrunken = true;
    g->arity = j;
    LOG (g->rhs, "shrunken %d [arity: %d] = XOR", g->lhs, g->arity);
  } else if (j != size){
    LOG (g->rhs, "shrinking gate to %d [arity: %d] = bigxor", g->lhs, g->arity);
    g->shrunken = true;
    g->rhs.resize(j);
    g->arity = j;
  }
  
  if (dst_count > 1)
    add_xor_shrinking_proof_chain (g, src);
  assert (internal->clause.empty());  
  update_xor_gate(g, git);

  if (!g->garbage && !internal->unsat && original_dst_negated &&
      dst_count == 1) {
    connect_goccs(g, dst);
  }

  check_xor_gate_implied(g);
  // TODO stats
  
}

void Closure::simplify_xor_gate (Gate *g) {
  LOG (g->rhs, "simplifying %d = %s", g->lhs, string_of_gate(g->tag).c_str());
  if (skip_xor_gate (g))
    return;
  unsigned negate = 0;
  GatesTable::iterator git = (g->indexed ? table.find(g) : end(table));
  const size_t size  = g->rhs.size();
  size_t j = 0;
  for (size_t i = 0; i < size; ++i) {
    int lit = g->rhs[i];
    assert (lit > 0);
    const signed char v = internal->val (lit);
    if (v > 0)
      negate ^= 1;
    if (!v)
      g->rhs[j++] = lit;
  }
  if (negate) {
    LOG ("flipping LHS literal %d", (g->lhs));
    g->lhs = - (g->lhs);
  }
  if (j != size) {
    LOG ("shrunken gate");
    g->shrunken = true;
    g->rhs.resize(j);
  }
  update_xor_gate (g, git);
  LOG (g->rhs, "simplified %d = XOR", g->lhs);
  check_xor_gate_implied (g);
  internal->stats.congruence.simplified++;
  internal->stats.congruence.simplified_xors++;
}

/*------------------------------------------------------------------------*/
// propagation of clauses and simplification
void Closure::schedule_literal(int lit) {
  const int idx = abs (lit);
  if (scheduled[idx])
    return;
  scheduled[idx] = true;
  schedule.push_back(lit);
  assert (lit != find_representative(lit));
  LOG ("scheduled literal %d", lit);
}

bool Closure::propagate_unit(int lit) {
  LOG("propagation of congruence unit %d", lit);
  return simplify_gates(lit) && simplify_gates(-lit);
}


bool Closure::propagate_units () {
  while (units != internal->trail.size())  {
    if (!propagate_unit(internal->trail[units++]))
      return false;
  }
  return true;
}

bool Closure::propagate_equivalence (int lit) {
  if (internal->val(lit))
    return true;
  const int repr = find_representative(lit);
  return rewrite_gates (repr, lit) && rewrite_gates (-repr, -lit);
}

size_t Closure::propagate_units_and_equivalences () {
  size_t propagated = 0;
  while (propagate_units() && !schedule.empty()) {
    ++propagated;
    int lit = schedule.back();
    LOG ("propagating equivalence of %d", lit);
    schedule.pop_back();
    scheduled[abs(lit)] = false;
    if (!propagate_equivalence(lit))
      break;
  }
  return propagated;
}


std::string string_of_gate (Gate_Type t) {
  switch(t) {
  case Gate_Type::And_Gate:
    return "And";
  case Gate_Type::XOr_Gate:
    return "XOr";
  case Gate_Type::ITE_Gate:
    return "ITE";
  default:
    return "buggy";
  }
}

void Closure::reset_closure() {
  scheduled.clear();
  for (Gate* g : table) {
    assert (g->indexed);
    LOG(g->rhs, "deleting gate %d = %s", g->lhs, string_of_gate (g->tag).c_str());
    if (!g->garbage)
      delete g;
  }
  table.clear();

  for (auto &occ : gtab) {
    occ.clear();
  }

  for (auto gate : garbage)
    delete gate;
  garbage.clear();
}

void Closure::forward_subsume_matching_clauses() {
  reset_closure();

  std::vector<signed char> matchable;
  matchable.resize (internal->max_var + 1);
  size_t count_matchable = 0;

  for (auto idx : internal->vars) {
    internal->occs(idx).clear();
    internal->occs(-idx).clear();
    if (!internal->flags(idx).active())
      continue;
    const int lit = idx;
    const int repr = find_representative(lit);
    if (lit == repr)
      continue;
    const int repr_idx = abs(repr);
    if (!matchable[idx]) {
      LOG ("matchable %d", idx);
      matchable[idx] = true;
      count_matchable++;
    }

    if(!matchable[repr_idx]) {
      LOG ("matchable %d", repr_idx);
      matchable[repr_idx] = true;
      count_matchable++;
    }
  }


  LOG ("found %.0f%%", count_matchable / (internal->max_var ? internal->max_var : 1));
  std::vector<Clause *> candidates;
  auto &analyzed = internal->analyzed;

  for (auto *c : internal->clauses) {
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    if (c->size == 2)
      continue;
    assert (analyzed.empty());
    bool contains_matchable = false;
    for (auto lit : *c) {
      const signed char v = internal->val(lit);
      if (v < 0)
	continue;
      if (v > 0) {
	LOG (c, "mark satisfied");
	internal->mark_garbage(c);
	break;
      }
      if (!contains_matchable) {
	const int idx = abs (lit);
	if (matchable[idx])
	  contains_matchable = true;
      }

      const int repr = find_representative (lit);
      assert (!internal->val (repr));
      if (marked (repr))
        continue;
      const int not_repr = -repr;
      if (marked (not_repr)) {
        LOG (c, "matches both %d and %d", (lit), (not_repr));
        internal->mark_garbage (c);
        break;
      }
      marked (repr) = 1;
      analyzed.push_back (repr);
    }

    for (auto lit : analyzed)
      marked (lit) = 0;
    analyzed.clear ();
    if (c->garbage)
      continue;
    if (!contains_matchable) {
      LOG ("no matching variable");
      continue;
    }
    candidates.push_back (c);
  }

  auto sort_order  = [&] (Clause *c, Clause *d) {
    return c->size < d->size || (c->size == d->size && c->id < d->id);
  };
  sort (begin (candidates), end (candidates), sort_order);
  size_t tried = 0, subsumed = 0;

  for (auto c : candidates) {
    assert (c->size != 2);
    // TODO if terminated
    ++tried;
    if (find_subsuming_clause (c)) {
      ++subsumed;
    }
  }
  LOG ("[congruence] subsumed %.0f%%",
       (double) subsumed / (double) (tried ? tried : 1));
}

bool Closure::find_subsuming_clause (Clause *subsumed) {
  assert (!subsumed->garbage);
  Clause *subsuming = nullptr;  
  for (auto lit : *subsumed) {
    assert (internal->val (lit) <= 0);
    const int repr_lit = find_representative (lit);
    const signed char repr_val = internal->val (repr_lit);
    assert (repr_val <= 0);
    if (repr_val < 0)
      continue;
    if (marked (repr_lit))
      continue;
    assert (!marked (-repr_lit));
    marked (repr_lit) = 1;
  }
  int least_occuring_lit = 0;
  size_t count_least_occurring = INT_MAX;
  LOG (subsumed, "trying to forward subsume");
  for (auto lit : *subsumed) {
    const int repr_lit = find_representative(lit);    
    const size_t count = internal->occs (lit).size ();
    assert (count <= UINT_MAX);
    if (count < count_least_occurring) {
      count_least_occurring = count;
      least_occuring_lit = repr_lit;
    }
    for (auto d : internal->occs (lit)) {
      assert (d->size != 2); // TODO might need an if here
      assert (!d->garbage);
      assert (subsumed != d);
      if (!subsumed->redundant && d->redundant)
        continue;
      for (auto other : *d) {
        const signed char v = internal->val (other);
        if (v < 0)
          continue;
        assert (!v);
        const int repr_other = find_representative (other);
        if (!marked (repr_other))
          goto CONTINUE_WITH_NEXT_CLAUSE;
      }
      subsuming = d;
      goto FOUND_SUBSUMING;

    CONTINUE_WITH_NEXT_CLAUSE:;
    }
  }
  assert (least_occuring_lit);
FOUND_SUBSUMING:
  for (auto lit : *subsumed) {
    const int repr_lit = find_representative (lit);
    const signed char v = internal->val (lit);
    if (!v)
      marked (repr_lit) = 0;
  }
  if (subsuming) {
    LOG (subsumed, "subsumed");
    LOG (subsuming, "subsuming");
    internal->subsume_clause (subsuming, subsumed);
    ++internal->stats.congruence.subsumed;
    return true;
  } else {
    internal->occs (least_occuring_lit).push_back (subsumed);
    return false;
  }
}

/*------------------------------------------------------------------------*/
void Closure::extract_gates() {
  extract_and_gates();
  if (internal->unsat)
    return;
  extract_xor_gates();
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
  init_watches ();
  connect_binary_watches ();
  Closure closure (this);
  init_occs();
  init_noccs();
  bool reset = false;

  closure.init_closure();
  closure.extract_gates ();
  if (!internal->unsat) {
    closure.find_units();
    if (!internal->unsat) {
      closure.find_equivalences();
      
      if (!internal->unsat) {
        const int propagated = closure.propagate_units_and_equivalences ();
        if (!internal->unsat && propagated)
	  closure.forward_subsume_matching_clauses();
	reset = true;
      }
    }
  }

  //if (!reset)
  closure.reset_closure();

  reset_occs();
  reset_noccs();
  reset_watches (); // TODO we could be more efficient here
  init_watches ();
  connect_watches ();
  
  if (!unsat && !internal->propagate())
    unsat = true;

  internal->report('=', !opts.reportall && !(stats.congruence.congruent - old));
}

}