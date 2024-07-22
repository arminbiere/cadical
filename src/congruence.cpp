#include "congruence.hpp"
#include "internal.hpp"
#include <iterator>
#include <vector>

namespace CaDiCaL {

#ifdef LOGGING
#define LOGGATE(g, str, ...) \
  LOG (g->rhs, str "%s gate[%d] (arity: %d) %d = %s", ##__VA_ARGS__, \
  g->garbage ? " garbage" : "", \
  g->id, g->arity, g->lhs, string_of_gate (g->tag).c_str ())
#else
#define LOGGATE(...) \
  while (false) {}
#endif
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
  LOGGATE (g, "marking as garbage");
  assert (!g->garbage);
  g->garbage = true;
  garbage.push_back(g);
}

bool Closure::remove_gate (GatesTable::iterator git) {
  assert (git != end (table));
  assert (!internal->unsat);
  (*git)->indexed = false;
  LOGGATE((*git), "removing from hash table");
  table.erase(git);
  return true;
}

bool Closure::remove_gate (Gate *g) {
  if (!g->indexed)
    return false;
  assert (!internal->unsat);
  assert (table.find(g) != end (table));
  table.erase(table.find(g));
  g->indexed = false;
  LOGGATE (g, "removing from hash table");
  return true;
}

void Closure::index_gate (Gate *g) {
  assert (!g->indexed);
  assert (!internal->unsat);
  assert (g->arity > 1);
  LOGGATE (g, "adding to hash table");
  table.insert(g);
  g->indexed = true;
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
  
  LOG ("propagating %zd %zd", internal->propagated, internal->trail.size());
  bool no_conflict = internal->propagate ();

  if (no_conflict)
    return true;
  internal->learn_empty_clause();

  return false;
}

bool Closure::merge_literals (int lit, int other) {
  assert (!internal->unsat);
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
    if (val_lit == -val_other) {
      LOG ("merging lits %d and %d assigned to inconsistent value", lit, other);
      internal->learn_empty_clause();
      return false;
    }

    assert (!val_other);
    LOG ("merging assigned %d and unassigned %d", lit, other);
    const unsigned unit = (val_lit < 0) ? -other : other;
    learn_congruence_unit(unit);
    return false;
  }

  if (!val_lit && val_other) {
    LOG ("merging assigned %d and unassigned %d", lit, other);
    const unsigned unit = (val_other < 0) ? -lit : lit;
    learn_congruence_unit(unit);
    return false;
  }

  int smaller = repr_lit;
  int larger = repr_other;

  if (abs(smaller) > abs(larger))
    swap (smaller, larger);

  assert (find_representative(smaller) == smaller);
  assert (find_representative(larger) == larger);

  if (repr_lit == -repr_other) {
    LOG ("merging clashing %d and %d", lit, other);
    internal->assign_unit (smaller);
    internal->learn_empty_clause();
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
#ifdef LOGGING
  fresh_id = internal->clause_id;
#endif  

}


void Closure::init_and_gate_extraction () {
  LOG ("[gate-extraction]");
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
void Closure::check_and_gate_implied (Gate *g) {
  assert (g->tag == Gate_Type::And_Gate);
  if (!internal->opts.check)
    return;
  LOGGATE (g, "checking implied");
  const int lhs = g->lhs;
  const int not_lhs = -lhs;
  for (auto other : g->rhs)
    check_binary_implied (not_lhs, other);
  internal->clause = g->rhs;
  check_implied ();
  internal->clause.clear();
}


void Closure::delete_proof_chain () {
  if (!internal->proof) {
    assert (chain.empty());
    return;
  }
  if (chain.empty())
    return;
#if 0
  chain.clear();  
  return; // temporary workaround
#endif
  LOG ("starting deletion of proof chain");
  auto &clause = internal->clause;
  assert (clause.empty());
  uint32_t id1 = UINT32_MAX, id2 = UINT32_MAX;
  uint64_t id = 0;

  LOG (chain, "chain:");
  for (auto lit : chain) {
    LOG ("reading %d from chain", lit);
    if (id1 == UINT32_MAX) {
      id1 = lit;
      id = (uint64_t) id1;
      continue;
    }
    if (id2 == UINT32_MAX) {
      id2 = lit;
      id = ((uint64_t) id1 << 32) + id2;
      continue;
    }
    if (lit) { // parsing the id first
      LOG ("found %d as literal in chain", lit);
      clause.push_back(lit);
    } else {
      assert (id);
      internal->proof->delete_clause (id, false, clause);
      clause.clear();
      id = 0, id1 = UINT32_MAX, id2 = UINT32_MAX;
    }
  }
  /* this is the version from kissat:
     std::vector<int>::const_iterator p = start;
  auto start = cbegin (chain);
  const auto end = cend (chain);
  while (p != end) {
    const int lit = *p;
    if (lit) { // parsing the id
      if (!id1) {
	id1 = lit;
	id = ((uint64_t)id1 << 32);
	continue;
      }
      if (!id2){
	id2 = lit;
	id = ((uint64_t)id1 << 32) + id2;
	continue;
      }
    }
    if (!lit) {
      while (start != p) {
        const int other = *start++;
	clause.push_back(other);
      }
      // TODO we need the id
      //internal->proof->delete_clause (internal->clause_id, false, clause);
      clause.clear();
      start++;
      id = 0, id1 = 0, id2 = 0;
    }
    p++;
  }
  assert (start == end);*/
  assert (clause.empty());
  chain.clear();
  LOG ("finished deletion of proof chain");
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
	  LOGGATE(g, "removing from table");
          (void)table.erase (it);
        }
        LOG (g->rhs, "inserting gate[%d] from table %d = %s", g->id, g->lhs,
             string_of_gate (g->tag).c_str ());
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
  assert (!internal->unsat && chain.empty ());
  LOGGATE(g, "updating");
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
    Gate *h = find_xor_gate (g);
    if (h) {
      assert (garbage);
      add_xor_matching_proof_chain (g, g->lhs, h->lhs);
      if (merge_literals (g->lhs, h->lhs))
        ++internal->stats.congruence.xors;
      if (!internal->unsat)
        delete_proof_chain ();
    } else {
      if (g->indexed) {
	remove_gate (git);
      }
      LOGGATE(g, "reinserting in table");
      table.insert (g);
      g->indexed = true;
      assert (table.find (g) != end (table));
      garbage = false;
    }
  }
  if (garbage && !internal->unsat)
    mark_garbage (g);
}

void Closure::simplify_and_gate (Gate *g) {
  if (skip_and_gate (g))
    return;
  GatesTable::iterator git = (g->indexed ? table.find(g) : end(table));
  LOG (g->rhs, "simplifying gate[%d] %d =", g->id, g->lhs);
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
    LOGGATE (g, "shrunken");
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
  case Gate_Type::ITE_Gate:
    simplify_ite_gate (g);
    break;
  default:
    assert (false);
    break;
  }

  return !internal->unsat;
  
}

bool Closure::simplify_gates (int lit) {
  const auto occs = goccs (lit);
  for (auto g : occs) {
    if (!simplify_gate (g))
      return false;
  }
  return true;  
}
/*------------------------------------------------------------------------*/
// AND gates


Gate *Closure::find_and_lits (int arity, const vector<int> &rhs) {
  return find_gate_lits(arity, rhs, Gate_Type::And_Gate);
}

// search for the gate in the hash-table.  We cannot use find, as we might be changing a gate, so
// there might be 2 gates with the same LHS (the one we are changing ang the other)
Gate *Closure::find_gate_lits (int arity, const vector<int> &rhs, Gate_Type typ, Gate *except) {
  Gate *g = new Gate;
  g->tag = typ;
  g->arity = arity;
  g->rhs = {rhs};
  g->lhs = 0;
#ifdef LOGGING
  g->id = 0;
#endif  
  const auto its = table.equal_range(g);
  Gate *h = nullptr;
  for (auto it = its.first; it != its.second; ++it) {
    if (*it == except)
      continue;
    h = *it;
    break;
  }

  if (h) {
    LOGGATE (h, "already existing");
    delete g;
    return h;
  }

  else { 
    LOG(g->rhs, "gate not found in table");
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
    g->lhs = lhs;
    g->tag = Gate_Type::And_Gate;
    g->arity = arity;
    g->rhs = {rhs};
    g->garbage = false;
    g->indexed = true;
    g->shrunken = false;
    g->ids.push_back(marked_mu1(-lhs));
    g->ids.push_back(marked_mu2(-lhs));
    g->ids.push_back(marked_mu4(-lhs));
    table.insert(g);
    ++internal->stats.congruence.gates;
    ++internal->stats.congruence.ands;
#ifdef LOGGING
    g->id = fresh_id++;
#endif  
    LOGGATE (g, "creating new");
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
  if (a_value > 0)
    return;
  const signed char b_value = internal->val (b);
  if (b_value > 0)
    return;
  int unit = 0;
  if (a == b)
    unit = a;
  else if (a_value < 0 && !b_value) {
    unit = b;
  } else if (!a_value && b_value < 0)
    unit = a;
  if (unit) {
    LOG ("clause reduced to unit %d", unit);
    learn_congruence_unit(unit);
    return;
  }
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
  LOG (c, "extracting and gates with clause");
  unsigned size = 0;
  const unsigned arity_limit =
      min (internal->opts.congruenceandarity, MAX_ARITY);
  const unsigned size_limit = arity_limit + 1;
  size_t max_negbincount = 0;
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
    const size_t count = internal->noccs (-lit);
    if (!count) {
      LOG (c,
           "%d negated does not occur in any binary clause, thus skipping",
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
         "all literals have less than %lu negated occurrences"
         "thus skipping",
         arity);
    return;
  }

  internal->analyzed.clear();
  size_t reduced = 0;
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
  LOG (c, "trying as base arity %lu AND gate", arity);
  sort (begin (lits), end (lits),
        [this] (int litA, int litB) {
          return (internal->noccs (-litA) < internal->noccs (-litB) ||
		  (internal->noccs (-litA) == internal->noccs (-litB) && litA < litB));
        });

  bool first = true;
  unsigned extracted = 0;

  for (size_t i = 0; i < clause_size; ++i) {
    if (internal->unsat)
      break;
    if (c->garbage)
      break;
    const int lhs = lits[i];
    LOG ("trying LHS candidate literal %d with %ld negated occurrences",
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
    LOG (c, "extracted %u with arity %lu AND base", extracted, arity);
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
  bool carry = true;
  for (size_t i = 0; i < lits.size() && carry; ++i) {
    int lit = lits[i];
    carry = (lit < 0);
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
  if (internal->proof) {
    internal->proof->add_derived_clause (internal->clause_id, false, clause, {});
    internal->proof->delete_clause (internal->clause_id, false, clause);
  }

  clause.clear();
}

void Closure::check_binary_implied (int a, int b) {
  if (!internal->opts.check)
    return;
  auto &clause = internal->clause;
  assert (clause.empty ());
  clause.push_back(a);
  clause.push_back(b);
  check_implied ();
  clause.clear();
}

void Closure::check_implied () {
  if (!internal->opts.check)
    return;
  internal->external->check_learned_clause ();
}

void Closure::add_xor_shrinking_proof_chain(Gate const *const g, int pivot) {
  if (!internal->proof)
    return;
  LOGGATE (g, "starting XOR shrinking proof chain");
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
    LOG (clause, "proof checking ");
    const uint64_t id1 = check_and_add_to_proof_chain (clause);
    clause.pop_back();
    clause.push_back(-pivot);
    const uint64_t id2 = check_and_add_to_proof_chain (clause);
    clause.pop_back();
    const uint64_t id3 = check_and_add_to_proof_chain (clause);
    if (internal->proof) {
      clause.push_back(pivot);
      internal->proof->delete_clause (id1, false, clause);
      clause.pop_back ();
      clause.push_back (-pivot);
      internal->proof->delete_clause (id2, false, clause);
      clause.pop_back();
    }
    inc_lits(clause);
  }
  clause.clear();
}

void Closure::check_xor_gate_implied(Gate const *const g) {
  assert (g->tag == Gate_Type::XOr_Gate);
  if (!internal->opts.check)
    return;
  const int lhs = g->lhs;
  LOGGATE (g, "checking implied");
  auto &clause = internal->clause;
  assert (clause.empty());
  for (auto other : g->rhs) {
    assert (other > 0);
    clause.push_back(other);
  }
  clause.push_back(-lhs);
  const unsigned arity = g->arity;
  const unsigned end = 1u << arity;
  const unsigned parity = (lhs > 0);

  for (unsigned i = 0; i != end; ++i) {
    while (i && parity_lits (clause) != parity)
      inc_lits (clause);
    internal->external->check_learned_clause ();
    if (internal->proof) {
      internal->proof->add_derived_clause (internal->clause_id, false,
                                           clause, {});
      internal->proof->delete_clause (internal->clause_id, false, clause);
    }
    inc_lits (clause);
  }
  clause.clear();
}
  
Gate* Closure::find_xor_lits (int arity, const vector<int> &rhs) {
  return find_gate_lits(arity, rhs, Gate_Type::XOr_Gate);
}

Gate* Closure::find_xor_gate (Gate *g) {
  assert (g->tag == Gate_Type::XOr_Gate);
  return find_gate_lits(g->arity, g->rhs, Gate_Type::XOr_Gate);
}


bool normalize_ite_lits (std::vector<int>& rhs) {
  assert (rhs.size() == 3);
  if (rhs[0] < 0) {
    rhs[0] = -rhs[0];
    std::swap(rhs[1], rhs[2]);
  }
  if (rhs[1] > 0)
    return false;
  rhs[1] = -rhs[1];
  rhs[2] = -rhs[2];
  return true;
}

Gate* Closure::find_ite_lits (int arity, vector<int> &rhs, bool& negate_lhs) {
  negate_lhs = normalize_ite_lits(rhs);
  return find_gate_lits(arity, rhs, Gate_Type::ITE_Gate);
}

Gate* Closure::find_ite_gate (Gate *g, bool& negate_lhs) {
  negate_lhs = normalize_ite_lits(g->rhs);
  return find_gate_lits(3, g->rhs, Gate_Type::ITE_Gate, g);
}

uint64_t Closure::check_and_add_to_proof_chain (vector<int> &clause) {
  internal->external->check_learned_clause ();
  const uint64_t id = ++internal->clause_id;
  if (internal->proof) {
    vector<uint64_t> lrat_chain;
    internal->proof->add_derived_clause (id, true,
                                         clause, lrat_chain);
  }
  return id;
}

void Closure::add_clause_to_chain (std::vector<int> unsimplified, uint64_t id) {
  const uint32_t id2_higher = (id >> 32);
  const uint32_t id2_lower = (uint32_t) (id & (uint64_t) (uint32_t) (-1));
  assert (id == ((uint64_t) id2_higher << 32) + (uint64_t) id2_lower);
  chain.push_back (id2_higher);
  chain.push_back (id2_lower);
  LOG (unsimplified, "pushing to chain"); 
  chain.insert (end (chain), begin (unsimplified), end (unsimplified));
  chain.push_back(0);
}

uint64_t Closure::simplify_and_add_to_proof_chain (
						   vector<int> &unsimplified, vector<int> &chain,
						    uint64_t delete_id) {
  vector<int> &clause = internal->clause;
  assert (clause.empty ());
#ifndef NDEBUG
  for (auto lit : unsimplified) {
    assert (!(marked (lit) & 4));
  }
#endif

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

  uint64_t id = 0;
  if (!trivial) {
    if (delete_id) {
      if (internal->proof)
        internal->proof->delete_clause (delete_id, true, clause);
    } else {
      id = check_and_add_to_proof_chain (clause);
      add_clause_to_chain (clause, id);
    }
  } else {
    LOG ("skipping trivial proof");
  }
  clause.clear ();
  return id;
}
/*------------------------------------------------------------------------*/
void Closure::add_ite_turned_and_binary_clauses (Gate *g) {
  if (!internal->proof)
    return;
  LOG ("starting ITE turned AND supporting binary clauses");
  assert (unsimplified.empty());
  assert (chain.empty());
  int not_lhs = -g->lhs;
  unsimplified.push_back(not_lhs);
  unsimplified.push_back(g->rhs[0]);
  simplify_and_add_to_proof_chain(unsimplified, chain);
  unsimplified.pop_back();
  unsimplified.push_back(g->rhs[1]);
  simplify_and_add_to_proof_chain(unsimplified, chain);
  unsimplified.clear();
}

void Closure::add_xor_matching_proof_chain(Gate *g, int lhs1, int lhs2) {
  if (lhs1 == lhs2)
    return;
  if (!internal->proof)
    return;
  unsimplified = g->rhs;
  
  LOG ("starting XOR matching proof");
  do {
    const size_t size = unsimplified.size();
    assert (size < 32);
    for (size_t i = 0; i != 1u << size; ++i) {
      unsimplified.push_back(-lhs1);
      unsimplified.push_back(lhs2);
      const uint64_t id1 = simplify_and_add_to_proof_chain (unsimplified, chain);
      unsimplified.resize(unsimplified.size() - 2);
      unsimplified.push_back(lhs1);
      unsimplified.push_back(-lhs2);
      const uint64_t id2 = simplify_and_add_to_proof_chain (unsimplified, chain);
      unsimplified.resize(unsimplified.size() - 2);
      // TODO we need to delete the original clauses, not the intermediate ones
      // generated here
      // but we need to remember the ids
      // if (false && internal->proof) {
      //   unsimplified.push_back (-lhs1);
      //   unsimplified.push_back (lhs2);
      //   simplify_and_add_to_proof_chain (unsimplified, chain, id1);
      //   unsimplified.resize (unsimplified.size () - 2);
      //   unsimplified.push_back (lhs1);
      //   unsimplified.push_back (-lhs2);
      //   simplify_and_add_to_proof_chain (unsimplified, chain, id2);
      // 	unsimplified.resize(unsimplified.size() - 2);
      // }
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
    if (!internal->unsat)
      delete_proof_chain();
    assert (internal->unsat || chain.empty ());
  } else {
    g = new Gate;
    g->lhs = lhs;
    g->tag = Gate_Type::XOr_Gate;
    g->arity = arity;
    g->rhs = {rhs};
    g->garbage = false;
    g->indexed = true;
    g->shrunken = false;
    table.insert(g);
    ++internal->stats.congruence.gates;
    ++internal->stats.congruence.xors;
#ifdef LOGGING
    g->id = fresh_id++;
#endif
    LOGGATE (g, "creating new");
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

  LOG ("considering %zd out of %zd", candidates.size(), internal->irredundant());
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
    glargecounts = std::move(gnew_largecounts);
    gnew_largecounts.clear();
    LOG ("moving counts %zd", glargecounts.size());
    if (!removed)
      break;

    LOG ("after round %d, %zd (%ld %%) remain", round, candidates.size(), candidates.size() / (1+original_size )* 100);
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
    if ((size_t)c->size<size_lits)
      continue;
    size_t found = 0;
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
  LOGGATE (g, "rewriting %d into %d in", src, dst);
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
  LOGGATE (g, "rewriten as");
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
  case Gate_Type::ITE_Gate:
    rewrite_ite_gate (g, dst, src);
    break;
  default:
    assert (false);
    break;
  }
  return !internal->unsat;
}

bool Closure::rewrite_gates(int dst, int src) {
  const auto &occs = goccs(src);
  for (auto g : occs) {
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
  if (skip_xor_gate (g))
    return;
  if (rewriting_lhs (g, dst))
    return;
  if (!gate_contains (g, src))
    return;
  LOGGATE (g, "rewriting (%d -> %d)", src, dst);
  check_xor_gate_implied (g);
  GatesTable::iterator git = (g->indexed ? table.find(g) : end(table));
  size_t j = 0, dst_count = 0;
  bool original_dst_negated = (dst < 0);
  dst = abs (dst);
  unsigned negate = original_dst_negated;
  const size_t size = g->rhs.size ();
  for (size_t i = 0; i < size; ++i) {
    int lit = g->rhs[i];
    assert (lit > 0);
    if (lit == src)
      lit = dst;
    const signed char v = internal->val (lit);
    if (v > 0) {
      negate ^= true;
      if (negate)
	LOG ("negate = %d due to %d with value %d", negate, lit, v);
    }
    if (v)
      continue;
    if (lit == dst)
      dst_count++;
    LOG ("keeping value %d", lit);
    g->rhs[j++] = lit;
  }
  if (negate) {
    LOG ("flipping LHS %d", g->lhs);
    g->lhs = -g->lhs;
  }
  assert (dst_count <= 2);
  if (dst_count == 2) {
    LOG ("destination found twice, removing");
    size_t k = 0;
    for (size_t i = 0; i < j; ++i) {
      const int lit = g->rhs[i];
      if (lit != dst)
	g->rhs[k++] = g->rhs[i];
    }
    assert (k == j - 2);
    g->rhs.resize(k);
    g->shrunken = true;
    g->arity = k;
  } else if (j != size){
    g->shrunken = true;
    g->rhs.resize(j);
    g->arity = j;
  }
  
  if (dst_count > 1)
    add_xor_shrinking_proof_chain (g, src);
  assert (g->arity == g->rhs.size());
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
  LOGGATE (g, "simplifying");
  if (skip_xor_gate (g))
    return;
  check_xor_gate_implied (g);
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
    if (!v) {
      g->rhs[j++] = lit;
    }
  }
  if (negate) {
    LOG ("flipping LHS literal %d", (g->lhs));
    g->lhs = - (g->lhs);
  }
  if (j != size) {
    LOG ("shrunken gate");
    g->shrunken = true;
    g->rhs.resize(j);
    g->arity = j;
  }
  assert (g->arity == g->rhs.size());
  check_xor_gate_implied (g);
  update_xor_gate (g, git);
  LOGGATE (g, "simplified");
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
  LOG ("propagation of congruence unit %d", lit);
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
    LOGGATE (g, "deleting");
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


  LOG ("found %.0f%%", (double)count_matchable / (double)(internal->max_var ? internal->max_var : 1));
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


/*------------------------------------------------------------------------*/
// Candidate clause 'subsumed' is subsumed by 'subsuming'.  We need to copy the function because
// 'congruence' is too early to include the version from subsume

void Closure::subsume_clause (Clause *subsuming, Clause *subsumed) {
  assert (!subsuming->redundant);
  assert (!subsumed->redundant);
  auto &stats = internal->stats;
  stats.subsumed++;
  assert (subsuming->size <= subsumed->size);
  LOG (subsumed, "subsumed");
  if (subsumed->redundant)
    stats.subred++;
  else
    stats.subirr++;
  if (subsumed->redundant || !subsuming->redundant) {
    internal->mark_garbage (subsumed);
    return;
  }
  LOG ("turning redundant subsuming clause into irredundant clause");
  subsuming->redundant = false;
  if (internal->proof)
    internal->proof->strengthen (subsuming->id);
  internal->mark_garbage (subsumed);
  stats.current.irredundant++;
  stats.added.irredundant++;
  stats.irrlits += subsuming->size;
  assert (stats.current.redundant > 0);
  stats.current.redundant--;
  assert (stats.added.redundant > 0);
  stats.added.redundant--;
  // ... and keep 'stats.added.total'.
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
    subsume_clause (subsuming, subsumed);
    ++internal->stats.congruence.subsumed;
    return true;
  } else {
    internal->occs (least_occuring_lit).push_back (subsumed);
    return false;
  }
}

/*------------------------------------------------------------------------*/
static bool skip_ite_gate (Gate *g) {
  assert (g->tag == Gate_Type::ITE_Gate);
  if (g->garbage)
    return true;
  return false;
}

void Closure::rewrite_ite_gate(Gate *g, int dst, int src) {
  if (skip_ite_gate(g))
    return;
  if (!gate_contains(g, src))
    return;
  LOGGATE (g, "rewriting %d by %d in", src, dst);
  assert (!g->shrunken);
  assert (g->arity == 3 && g->rhs.size() == 3);
  auto &rhs = g->rhs;
  const int lhs = g->lhs;
  const int cond = g->rhs[0];
  const int then_lit = g->rhs[1];
  const int else_lit = g->rhs[2];
  const int not_lhs = - (lhs);
  const int not_dst = - (dst);
  const int not_cond = - (cond);
  const int not_then_lit = - (then_lit);
  const int not_else_lit = - (else_lit);
  Gate_Type new_tag = Gate_Type::And_Gate;

  bool garbage = false;
  bool shrink = true;
  const auto git = g->indexed ? table.find (g) : end (table);
  assert (!g->indexed || git != end (table));
  assert (*git == g);  
  // this code is taken one-to-one from kissat
  if (src == cond) {
    if (dst == then_lit) {
      // then_lit ? then_lit : else_lit
      // then_lit & then_lit | !then_lit & else_lit
      // then_lit | !then_lit & else_lit
      // then_lit | else_lit
      // !(!then_lit & !else_lit)
      g->lhs = not_lhs;
      rhs[0] = not_then_lit;
      rhs[1] = not_else_lit;
    } else if (not_dst == then_lit) {
      // !then_lit ? then_lit : else_lit
      // !then_lit & then_lit | then_lit & else_lit
      // then_lit & else_lit
      rhs[0] = else_lit;
      assert (rhs[1] == then_lit);
    } else if (dst == else_lit) {
      // else_list ? then_lit : else_lit
      // else_list & then_lit | !else_list & else_lit
      // else_list & then_lit
      rhs[0] = else_lit;
      assert (rhs[1] == then_lit);
    } else if (not_dst == else_lit) {
      // !else_list ? then_lit : else_lit
      // !else_list & then_lit | else_lit & else_lit
      // !else_list & then_lit | else_lit
      // then_lit | else_lit
      // !(!then_lit & !else_lit)
      g->lhs = not_lhs;
      rhs[0] = not_then_lit;
      rhs[1] = not_else_lit;
    } else {
      shrink = false;
      rhs[0] = dst;
    }
  } else if (src == then_lit) {
    if (dst == cond) {
      // cond ? cond : else_lit
      // cond & cond | !cond & else_lit
      // cond | !cond & else_lit
      // cond | else_lit
      // !(!cond & !else_lit)
      g->lhs = not_lhs;
      rhs[0] = not_cond;
      rhs[1] = not_else_lit;
    } else if (not_dst == cond) {
      // cond ? !cond : else_lit
      // cond & !cond | !cond & else_lit
      // !cond & else_lit
      rhs[0] = not_cond;
      rhs[1] = else_lit;
    } else if (dst == else_lit) {
      // cond ? else_lit : else_lit
      // else_lit
      if (merge_literals (lhs, else_lit)) {
	++internal->stats.congruence.unaries;
	++internal->stats.congruence.unary_ites;
      }
      garbage = true;
    } else if (not_dst == else_lit) {
      // cond ? !else_lit : else_lit
      // cond & !else_lit | !cond & else_lit
      // cond ^ else_lit
      new_tag = Gate_Type::XOr_Gate;
      assert (rhs[0] == cond);
      rhs[1] = else_lit;
    } else {
      shrink = false;
      rhs[1] = dst;
    }
  } else {
    assert (src == else_lit);
    if (dst == cond) {
      // cond ? then_lit : cond
      // cond & then_lit | !cond & cond
      // cond & then_lit
      assert (rhs[0] == cond);
      assert (rhs[1] == then_lit);
    } else if (not_dst == cond) {
      // cond ? then_lit : !cond
      // cond & then_lit | !cond & !cond
      // cond & then_lit | !cond
      // then_lit | !cond
      // !(!then_lit & cond)
      g->lhs = not_lhs;
      assert (rhs[0] == cond);
      rhs[1] = not_then_lit;
    } else if (dst == then_lit) {
      // cond ? then_lit : then_lit
      // then_lit
      if (merge_literals (lhs, then_lit)) {
	++internal->stats.congruence.unaries;
	++internal->stats.congruence.unary_ites;
      }
      garbage = true;
    } else if (not_dst == then_lit) {
      // cond ? then_lit : !then_lit
      // cond & then_lit | !cond & !then_lit
      // !(cond ^ then_lit)
      new_tag = Gate_Type::XOr_Gate;
      g->lhs = not_lhs;
      assert (rhs[0] == cond);
      assert (rhs[1] == then_lit);
    } else {
      shrink = false;
      rhs[2] = dst;
    }
  }
  

  if (!garbage) {
    if (shrink) {
      if (new_tag == Gate_Type::XOr_Gate) {
        bool negate_lhs = false;
        if (rhs[0] < 0) {
          rhs[0] = -rhs[0];
          negate_lhs = !negate_lhs;
        }
        if (rhs[1] < 0) {
          rhs[1] = -rhs[1];
          negate_lhs = !negate_lhs;
        }
        if (negate_lhs)
          g->lhs = -g->lhs;
      }
      if (rhs[0] > rhs[1]) // unlike kissat, we need to do it after negating 
	std::swap(rhs[0], rhs[1]);
      assert (rhs[0] < rhs[1]);
      assert (!g->shrunken);
      g->shrunken = true;
      rhs[2] = 0;
      g->arity = 2;
      g->tag = new_tag;
      g->rhs.resize(2);
      assert (rhs[0] < rhs[1]);
      assert (rhs[0] != -rhs[1]);
      LOGGATE (g, "rewritten");
      Gate *h;
      if (new_tag == Gate_Type::And_Gate) {
        check_and_gate_implied (g);
        h = find_and_lits (g->lhs, g->rhs);
      } else {
        assert (new_tag == Gate_Type::XOr_Gate);
        check_xor_gate_implied (g);
        h = find_xor_lits (g->lhs, g->rhs);
      }
      if (h) {
        garbage = true;
        if (new_tag == Gate_Type::XOr_Gate)
          add_xor_matching_proof_chain (g, g->lhs, h->lhs);
        else
          add_ite_turned_and_binary_clauses (g);
        if (merge_literals (g->lhs, h->lhs))
	  ++internal->stats.congruence.ands;
        if (!internal->unsat)
          delete_proof_chain ();
      } else {
        garbage = false;
	if (g->indexed)
          remove_gate (git);
        index_gate (g);
        assert (g->arity == 2);
        for (auto lit : g->rhs)
          if (lit != dst)
            if (lit != cond && lit != then_lit && lit != else_lit)
              connect_goccs (g, lit);
        if (g->tag == Gate_Type::And_Gate)
          for (auto lit : g->rhs)
            add_binary_clause (-g->lhs, lit);
      }
    } else {
      LOGGATE (g, "rewritten");
      assert (rhs[0] != rhs[1]);
      assert (rhs[0] != rhs[2]);
      assert (rhs[1] != rhs[2]);
      assert (rhs[0] != - (rhs[1]));
      assert (rhs[0] != - (rhs[2]));
      assert (rhs[1] != - (rhs[2]));
      check_ite_gate_implied (g);
      bool negate_lhs;
      Gate *h = find_ite_gate (g, negate_lhs);
      assert (lhs == g->lhs);
      assert (not_lhs == - (g->lhs));
      if (h) {
        garbage = true;
	LOG ("checking h");
	check_ite_gate_implied(h);
	LOG ("checking G");
	check_ite_gate_implied(g);
        int normalized_lhs = negate_lhs ? not_lhs : lhs;
        add_ite_matching_proof_chain (h, h->lhs, normalized_lhs);
        if (merge_literals (h->lhs, normalized_lhs))
	  ++internal->stats.congruence.ites;
        if (!internal->unsat)
          delete_proof_chain ();
	assert (internal->unsat || chain.empty ());
      } else {
        garbage = false;
	if (g->indexed)
          remove_gate (git);
        if (negate_lhs)
          g->lhs = not_lhs;
        LOGGATE (g, "normalized");
        index_gate (g);
        assert (g->arity == 3);
        for (auto lit : g->rhs)
          if (lit != dst)
            if (lit != cond && lit != then_lit && lit != else_lit)
              connect_goccs (g, lit);
      }
    }
  }
  if (garbage && !internal->unsat)
    mark_garbage (g);

  if (!internal->unsat)
    assert (chain.empty ());
}

void Closure::simplify_ite_gate (Gate *g) {
  if (skip_ite_gate (g))
    return;
  assert (g->arity == 3);
  bool garbage = true;
  int lhs = g->lhs;
  auto &rhs = g->rhs;
  const int cond = rhs[0];
  const int then_lit = rhs[1];
  const int else_lit = rhs[2];
  const signed char v_cond = internal->val (cond);
  if (v_cond > 0) {
    if (merge_literals(lhs, then_lit)) {
      ++internal->stats.congruence.unary_ites;
      ++internal->stats.congruence.unaries;
    }
  } else if (v_cond < 0) {
    if (merge_literals(lhs, else_lit)) {
      ++internal->stats.congruence.unary_ites;
      ++internal->stats.congruence.unaries;
    }
  } else {
    const signed char v_else = internal->val (else_lit);
    const signed char v_then = internal->val (then_lit);
    assert (v_then || v_else);
    if (v_then > 0 && v_else > 0) {
      learn_congruence_unit (lhs);
    } else if (v_then < 0 && v_else < 0) {
      learn_congruence_unit (-lhs);
    } else if (v_then > 0 && v_else < 0) {
      if (merge_literals (lhs, cond)) {
        ++internal->stats.congruence.unary_ites;
        ++internal->stats.congruence.unaries;
      }
    } else if (v_then < 0 && v_else > 0) {
      if (merge_literals (lhs, -cond)) {
        ++internal->stats.congruence.unary_ites;
        ++internal->stats.congruence.unaries;
      }
    } else {
      assert (!!v_then + !!v_else == 1);
      auto git = g->indexed ? table.find (g) : end (table);
      assert (!g->indexed || git != end (table));
      if (v_then > 0) {
	g->lhs = -lhs;
	rhs[0] = -cond;
	rhs[1] = -else_lit;
      } else if (v_then < 0) {
	rhs[0] = -cond;
	rhs[1] = else_lit;
	
      } else if (v_else > 0) {
	g->lhs = -lhs;
	rhs[0] = -then_lit;
	rhs[1] = cond;
	
      } else {
	assert (v_else < 0);
	rhs[0] = cond;
	rhs[1] = then_lit;
      }
      if (internal->vlit (rhs[0]) > internal->vlit (rhs[1]))
	std::swap (rhs[0], rhs[1]);
      g->shrunken = true;
      g->tag = Gate_Type::And_Gate;
      g->arity = 2;
      rhs.resize(2);
      check_and_gate_implied(g);
      Gate *h = find_and_lits(2, rhs);
      if (h) {
	assert (garbage);
	if (merge_literals(g->lhs, h->lhs)) {
	  ++internal->stats.congruence.ands;
	}
      } else {
	remove_gate(git);
	index_gate(g);
	garbage = false;
	for (auto lit : rhs)
	  if (lit != cond && lit != then_lit && lit != else_lit) {
	    connect_goccs(g, lit);
	  }
      }
    }
  } 
  if (garbage && !internal->unsat)
    mark_garbage(g);
  ++internal->stats.congruence.simplified;
  ++internal->stats.congruence.simplified_ites;
}

void Closure::add_ite_matching_proof_chain (Gate *g, int lhs1, int lhs2) {
  if (lhs1 == lhs2)
    return;
  if (!internal->proof)
    return;
  LOG ("starting ITE matching proof chain");
  assert (unsimplified.empty ());

  assert (chain.empty ());
  const auto &rhs = g->rhs;
  const int cond = rhs[0];
  unsimplified.push_back (lhs1);
  unsimplified.push_back (-lhs2);
  unsimplified.push_back (cond);
  const uint64_t id1 =
      simplify_and_add_to_proof_chain (unsimplified, chain);
  unsimplified.pop_back ();
  unsimplified.push_back (-cond);
  const uint64_t id2 =
    simplify_and_add_to_proof_chain (unsimplified, chain);
  unsimplified.pop_back ();
  const uint64_t id = check_and_add_to_proof_chain (unsimplified);
  add_clause_to_chain (unsimplified, id);
  unsimplified.clear();
  unsimplified.push_back (-lhs1);
  unsimplified.push_back (lhs2);
  unsimplified.push_back (cond);
  const uint64_t id3 = simplify_and_add_to_proof_chain (unsimplified, chain);
  unsimplified.pop_back ();
  unsimplified.push_back (-cond);
  const uint64_t id4 = simplify_and_add_to_proof_chain (unsimplified, chain);
  unsimplified.pop_back ();
  const uint64_t id5 = simplify_and_add_to_proof_chain (unsimplified, chain);
  unsimplified.clear ();
  LOG ("finished ITE matching proof chain");
}


Gate *Closure::new_ite_gate (int lhs, int cond, int then_lit,
                             int else_lit) {

  if (else_lit == -then_lit) {
    if (then_lit < 0)
      LOG ("skipping ternary XOR %d := %d ^ %d", lhs, cond, -then_lit);
    else
      LOG ("skipping ternary XOR %d := %d ^ %d", -lhs, cond, then_lit);
    return nullptr;
  }
  if (else_lit == then_lit) {
    LOG ("found trivial ITE gate %d := %d ? %d : %d", (lhs), (cond),
         (then_lit), (else_lit));
    if (merge_literals (lhs, then_lit))
      ++internal->stats.congruence.trivial_ite;
    return 0;
  }

  rhs.clear ();
  rhs.push_back (cond);
  rhs.push_back (then_lit);
  rhs.push_back (else_lit);
  const unsigned arity = 3;
  LOG ("ITE gate %d = %d ? %d : %d", lhs, cond, then_lit, else_lit);

  bool negate_lhs = false;
  Gate *g = find_ite_lits (arity, this->rhs, negate_lhs);
  if (negate_lhs)
    lhs = -lhs;
  if (g) {
    check_ite_gate_implied (g);
    add_ite_matching_proof_chain (g, g->lhs, lhs);
    if (merge_literals (g->lhs, lhs)) {
      ++internal->stats.congruence.ites;
      LOG ("found merged literals");
    }
    if (!internal->unsat)
      delete_proof_chain ();
  } else {
    g = new Gate;
    g->lhs = lhs;
    g->tag = Gate_Type::ITE_Gate;
    g->arity = arity;
    g->rhs = {rhs};
    g->garbage = false;
    g->indexed = true;
    g->shrunken = false;
    table.insert (g);
    ++internal->stats.congruence.gates;
    ++internal->stats.congruence.xors;
#ifdef LOGGING
    g->id = fresh_id++;
#endif
    LOGGATE (g, "creating new");
    check_ite_gate_implied (g);
    for (auto lit : g->rhs) {
      connect_goccs (g, lit);
    }
  }
  return g;
}

void check_ite_lits_normalized (std::vector<int> lits) {
  assert (lits[0] > 0);
  assert (lits[1] > 0);
  assert (lits[0] != lits[1]);
  assert (lits[0] != lits[2]);
  assert (lits[1] != lits[2]);
  assert (lits[0] != -lits[1]);
  assert (lits[0] != -lits[2]);
  assert (lits[1] != -lits[2]);
}

void Closure::check_ite_implied (int lhs, int cond, int then_lit, int else_lit) {
  if (!internal->opts.check)
    return;
  check_ternary(cond, -else_lit, lhs);
  check_ternary(cond, else_lit, -lhs);
  check_ternary(-cond, -then_lit, lhs);
  check_ternary(-cond, then_lit, -lhs);
}

void Closure::check_ite_gate_implied (Gate *g) {
  assert (g->tag == Gate_Type::ITE_Gate);
  if (!internal->opts.check)
    return;
  check_ite_implied (g->lhs, g->rhs[0], g->rhs[1], g->rhs[2]);
}

void Closure::init_ite_gate_extraction (std::vector<Clause *> &candidates) {
  std::vector<Clause *> ternary;
  glargecounts.resize (2 * internal->vsize, 0);
  for (auto lit : internal->lits) {
    // TODO where is kissat doing that?
    internal->occs (lit).clear ();
    internal->occs (-lit).clear ();
  }
  for (auto c : internal->clauses) {
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    unsigned size = 0;

    assert (!c->garbage);
    for (auto lit : *c) {
      const signed char v = internal->val (lit);
      if (v < 0)
	continue;
      if (v > 0) {
	LOG (c, "deleting as satisfied due to %d", lit);
	internal->mark_garbage(c);
        goto CONTINUE_COUNTING_NEXT_CLAUSE;
      }
      if (size == 3)
        goto CONTINUE_COUNTING_NEXT_CLAUSE;
      size++;
    }
    if (size < 3)
      continue;
    assert (size == 3);
    ternary.push_back(c);
    LOG (c, "counting original ITE gate base");
    for (auto lit : *c) {
      if (!internal->val (lit))
	++largecount(lit);
    }
  CONTINUE_COUNTING_NEXT_CLAUSE:;
  }

  for (auto c : ternary) {
    assert (!c->garbage);
    assert (!c->redundant);
    unsigned positive = 0, negative = 0, twice = 0;
    for (auto lit : *c) {
      if (internal->val (lit))
	continue;
      const int count_not_lit = largecount (-lit);
      if (!count_not_lit)
        goto CONTINUE_WITH_NEXT_TERNARY_CLAUSE;
      const unsigned count_lit = largecount(lit);
      assert (count_lit);
      if (count_lit > 1 && count_not_lit > 1)
	++twice;
      if (lit < 0)
	++negative;
      else
	++positive;
    }
    if (twice < 2)
      goto CONTINUE_WITH_NEXT_TERNARY_CLAUSE;
    for (auto lit : *c)
      internal->occs (lit).push_back(c);
    internal->watch_clause(c);
    if (positive && negative)
      candidates.push_back(c);
  CONTINUE_WITH_NEXT_TERNARY_CLAUSE:;
  }

  ternary.clear();
}

void Closure::reset_ite_gate_extraction () {
  condbin[0].clear();
  condbin[1].clear();
  condeq[0].clear();
  condeq[1].clear();
  glargecounts.clear();
}

void Closure::copy_conditional_equivalences (int lit, std::vector<std::pair<int, int>> &condbin) {
  assert (condbin.empty());
  for (auto c : internal->occs (lit)) {
    assert(c->size != 2);
    int first = 0, second = 0;
    for (auto other : *c) {
      if (internal->val(other))
	continue;
      if (other == lit)
	continue;
      if (!first)
	first = other;
      else {
	assert (!second);
	second = other;
      }
    }
    assert (first), assert (second);
    std::pair<int, int> p;
    
    if (internal->vlit (first) < internal->vlit (second))
      p.first = first, p.second = second;
    else {
      assert (internal->vlit (second) < internal->vlit (first));
      p.first = second, p.second = first;
    }
    LOG ("literal %d condition binary clause %d %d", lit, first, second);
    condbin.push_back(p);
  }
}

bool less_litpair (litpair p, litpair q) {
  const int a = p.first;
  const int b = q.first;
  if (a < b)
    return true;
  if (b > a)
    return false;
  const int c = p.second;
  const int d = q.second;
  return (c < d);
}
struct litpair_rank {
  CaDiCaL::Internal *internal;
  litpair_rank  (Internal *i) : internal (i) {}
  typedef uint64_t Type;
  Type operator() (const litpair &a) const {
    uint64_t lita = internal->vlit(a.first);
    uint64_t litb = internal->vlit(a.second);
    return (lita<<32) + litb;
  }
};

struct litpair_smaller {
  CaDiCaL::Internal *internal;
  litpair_smaller (Internal *i) : internal (i) {}
  bool operator() (const litpair &a, const litpair &b) const {
    const auto s = litpair_rank (internal) (a);
    const auto t = litpair_rank (internal) (b);
    return s < t;
  }
};


bool Closure::find_litpair_second_literal (int lit, litpairs::const_iterator begin,
                                  litpairs::const_iterator end) {
  LOG ("searching for %d in", lit);
  for (auto it = begin; it != end; ++it)
    LOG ("%d [%d]", it->first, it->second);
  auto found = std::binary_search(begin, end, std::pair<int,int>{lit, lit}, [](const litpair& a, const litpair &b) {
    return a.second < b.second;
  });
  return found;
/*
  litpairs::const_iterator l = begin, r = end;
  while (l != r) {
    litpairs::const_iterator m = l + (r - l) / 2;
    assert (begin <= m), assert (m < end);
    int other = m->second;
    if (other < lit)
      l = m + 1;
    else if (other > lit)
      r = m;
    else
      return true;
  }
  return false;
*/
}

void Closure::search_condeq (int lit, int pos_lit,
                             litpairs::const_iterator pos_begin,
                             litpairs::const_iterator pos_end, int neg_lit,
                             litpairs::const_iterator neg_begin,
                             litpairs::const_iterator neg_end,
                             litpairs &condeq) {
  assert (neg_lit == - pos_lit);
  assert (pos_begin < pos_end);
  assert (neg_begin < neg_end);
  assert (pos_begin->first == pos_lit);
  assert (neg_begin->first == neg_lit);
  assert (pos_end <= neg_begin || neg_end <= pos_begin);
  for (litpairs::const_iterator p = pos_begin; p != pos_end; p++) {
    const int other = p->second;
    const int not_other = -other;
    if (find_litpair_second_literal (not_other, neg_begin, neg_end)) {
      int first, second;
      if (pos_lit < 0)
        first = neg_lit, second = other;
      else
        first = pos_lit, second = not_other;
      LOG ("found conditional %d equivalence %d = %d", lit, first,  second);
      assert (first > 0);
      assert (internal->vlit (first) < internal->vlit (second));
      check_ternary (lit, first, -second);
      check_ternary (lit, -first, second);
      std::pair<int, int> equivalence = {first, second};
      condeq.push_back(equivalence);
      if (second < 0) {
	std::pair<int, int> inverse_equivalence = {-second, -first};
	condeq.push_back(inverse_equivalence);
      } else {
	std::pair<int, int> inverse_equivalence = {second, first};
	condeq.push_back(inverse_equivalence);
      }
    }
  }
#ifndef LOGGING
  (void) lit;
#endif
}

void Closure::extract_condeq_pairs (int lit, litpairs &condbin, litpairs &condeq) {
  const litpairs::const_iterator begin = condbin.cbegin();
  const litpairs::const_iterator end = condbin.cend();
  litpairs::const_iterator pos_begin = begin;
  int next_lit = 0;
  
  for (const auto &pair : condbin)
    LOG ("unsorted conditional %d equivalence %d = %d",  lit, pair.first,  pair.second);
  LOG ("searching for first positive literal for lit %d", lit);
  for (;;) {
    if (pos_begin == end)
      return;
    next_lit = pos_begin->first;
    LOG ("checking %d", next_lit);
    if (next_lit > 0)
      break;
    pos_begin++;
  }

  for (;;) {
    assert (pos_begin != end);
    assert (next_lit == pos_begin->first);
    assert (next_lit > 0);
    const int pos_lit = next_lit;
    litpairs::const_iterator pos_end = pos_begin + 1;
    LOG ("searching for first other literal after finding lit %d", next_lit);
    for (;;) {
      if (pos_end == end)
        return;
      next_lit = pos_end->first;
      if (next_lit != pos_lit)
        break;
      pos_end++;
    }
    assert (pos_end != end);
    assert (next_lit == pos_end->first);
    const int neg_lit = -pos_lit;
    if (next_lit != neg_lit) {
      if (next_lit < 0) {
        pos_begin = pos_end + 1;
	LOG ("next_lit %d < 0", next_lit);
        for (;;) {
          if (pos_begin == end)
            return;
          next_lit = pos_begin->first;
          if (next_lit > 0)
            break;
          pos_begin++;
        }
      } else
        pos_begin = pos_end;
      continue;
    }
    const litpairs::const_iterator neg_begin = pos_end;
    litpairs::const_iterator neg_end = neg_begin + 1;
    while (neg_end != end) {
      next_lit = neg_end->first;
      if (next_lit != neg_lit)
        break;
      neg_end++;
    }
#ifdef LOGGING
    for (litpairs::const_iterator p = pos_begin; p != pos_end; p++)
      LOG ("conditional %d binary clause %d %d with positive %d",
            (lit),  (p->first),  (p->second),
            (pos_lit));
    for (litpairs::const_iterator p = neg_begin; p != neg_end; p++)
      LOG ("conditional %d binary clause %d %d with negative %d",
            (lit),  (p->first),  (p->second),
            (neg_lit));
#endif
    const size_t pos_size = pos_end - pos_begin;
    const size_t neg_size = neg_end - neg_begin;
    if (pos_size <= neg_size) {
      LOG ("searching negation of %zu conditional binary clauses "
           "with positive %d in %zu conditional binary clauses with %d",
           pos_size, (pos_lit), neg_size, (neg_lit));
      search_condeq (lit, pos_lit, pos_begin, pos_end, neg_lit, neg_begin, neg_end, condeq);
    } else {
      LOG ("searching negation of %zu conditional binary clauses "
           "with negative %d in %zu conditional binary clauses with %d",
           neg_size, (neg_lit), pos_size, (pos_lit));
      search_condeq (lit, neg_lit, neg_begin, neg_end, pos_lit, pos_begin, pos_end, condeq);
    }
    if (neg_end == end)
      return;
    assert (next_lit == neg_end->first);
    if (next_lit < 0) {
      pos_begin = neg_end + 1;
      for (;;) {
        if (pos_begin == end)
          return;
        next_lit = pos_begin->first;
        if (next_lit > 0)
          break;
        pos_begin++;
      }
    } else
      pos_begin = neg_end;
  }
}

void Closure::find_conditional_equivalences (
    int lit,
    std::vector<std::pair<int, int>> &condbin,
    std::vector<std::pair<int, int>> &condeq) {
  assert (condbin.empty());
  assert (condeq.empty());
  assert (internal->occs (lit).size () > 1);
  copy_conditional_equivalences(lit, condbin);
  MSORT (internal->opts.radixsortlim, begin (condbin), end (condbin),
         litpair_rank (this->internal), litpair_smaller (this->internal));
 
  extract_condeq_pairs (lit, condbin, condeq);
  MSORT (internal->opts.radixsortlim, begin (condbin), end (condbin),
         litpair_rank (this->internal), litpair_smaller (this->internal));

#ifdef LOGGING
  for (auto pair : condeq)
    LOG ("sorted conditional %d equivalence %d = %d",  lit, pair.first,  pair.second);
  LOG ("found %zu conditional %d equivalences", condeq.size(), lit);

#endif
}


void Closure::merge_condeq (int cond, litpairs & condeq, litpairs & not_condeq) {
  LOG ("merging cond for literal %d", cond);
  auto q = begin (not_condeq);
  const auto end_not_condeq = end (not_condeq);
  for (auto p : condeq) {
    const int lhs = p.first;
    const int then_lit = p.second;
    assert (lhs > 0);
    while (q != end_not_condeq && q->first < lhs)
      ++q;
    while (q != end_not_condeq && q->first == lhs){
      litpair not_cond_pair = *q++;
      const int else_lit = not_cond_pair.second;
      new_ite_gate (lhs, cond, then_lit, else_lit);
      if (internal->unsat)
	return;
    }
    
  }
}

void Closure::extract_ite_gates_of_literal (int lit) {
  LOG ("search for ITE for literal %d ", lit);
  find_conditional_equivalences(lit, condbin[0], condeq[0]);
  if (!condeq[0].empty()) {
    find_conditional_equivalences(-lit, condbin[1], condeq[1]);
    if (!condeq[1].empty()) {
      if (lit < 0)
        merge_condeq(-lit, condeq[0], condeq[1]);
      else
	merge_condeq(lit, condeq[1], condeq[0]);
    }
  }

  condbin[0].clear();
  condbin[1].clear();
  condeq[0].clear();
  condeq[1].clear();
}

void Closure::extract_ite_gates_of_variable (int idx) {
  const int lit = idx;
  const int not_lit = -idx;

  auto lit_watches = internal->occs (lit);
  auto not_lit_watches = internal->occs (not_lit);
  const size_t size_lit_watches = lit_watches.size();
  const size_t size_not_lit_watches = not_lit_watches.size();
  if (size_lit_watches <= size_not_lit_watches) {
    if (size_lit_watches > 1)
      extract_ite_gates_of_literal (lit);
  } else {
    if (size_not_lit_watches > 1)
      extract_ite_gates_of_literal (not_lit);
  }
}

void Closure::extract_ite_gates() {
  if (!internal->opts.congruenceite)
    return;
  std::vector<Clause*> candidates;
  init_ite_gate_extraction(candidates);

  for (auto idx : internal->vars) {
    if (internal->flags(idx).active()) {
      extract_ite_gates_of_variable(idx);
      if (internal->unsat)
	break;
    }
  }
  // Kissat has an alternative version MERGE_CONDITIONAL_EQUIVALENCES
  reset_ite_gate_extraction();
  candidates.clear();
}
/*------------------------------------------------------------------------*/
void Closure::extract_gates() {
  extract_and_gates();
  if (internal->unsat)
    return;
  extract_xor_gates();
  if (internal->unsat)
    return;
  extract_ite_gates();
}

/*------------------------------------------------------------------------*/
// top lever function to exctract gate
void Internal::extract_gates () {
  if (unsat)
    return;
  if (!opts.congruence)
    return;
  if (level)
    backtrack ();
  if (!propagate ()) {
    learn_empty_clause ();
    return;
  }

  const int64_t old = stats.congruence.congruent;
  const bool dedup = opts.deduplicate;
  const int old_merged = stats.congruence.congruent;
  opts.deduplicate = true;
  mark_duplicated_binary_clauses_as_garbage ();
  opts.deduplicate = dedup;
  ++stats.congruence.rounds;
  reset_watches (); // saves lots of memory
  init_watches ();
  connect_binary_watches ();
  Closure closure (this);
  init_occs();
  init_noccs ();

  closure.init_closure ();
  assert (unsat || closure.chain.empty ());
  closure.extract_gates ();
  assert (unsat || closure.chain.empty ());
  if (!unsat) {
    closure.find_units ();
    assert (unsat || closure.chain.empty ());
    if (!internal->unsat) {
      closure.find_equivalences ();
      assert (unsat || closure.chain.empty ());

      if (!unsat) {
        const int propagated = closure.propagate_units_and_equivalences ();
        assert (unsat || closure.chain.empty ());
        if (!unsat && propagated)
          closure.forward_subsume_matching_clauses ();
      }
    }
  }

  closure.reset_closure();

  reset_occs();
  reset_noccs();
  reset_watches (); // TODO we could be more efficient here
  init_watches ();
  connect_watches ();
  
  const int64_t new_merged = stats.congruence.congruent;

  phase ("congruence-phase", stats.congruence.rounds,
	 "merged %ld literals", new_merged - old_merged);
  if (!unsat && !internal->propagate())
    unsat = true;


  report('=', !opts.reportall && !(stats.congruence.congruent - old));

  if (opts.decompose && new_merged != old_merged) {
    decompose ();
    this->report('d', !opts.reportall && !(stats.congruence.congruent - old));
  }
}

}