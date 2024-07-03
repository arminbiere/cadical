#include "internal.hpp"

namespace CaDiCaL {

 
  
bool Internal::factoring () {
  if (!opts.factor) return false;
  if (stats.factor >= opts.factorrounds) return false;
  return stats.conflicts > stats.factor * 3000;
}

// essentially do full occurence list as in elim.cpp
void Internal::factor_mode (Factorizor &factor) {
  reset_watches ();

  assert (!watching ());
  // init_noccs ();
  // init_occs ();
  factor.occurs.resize (2 * vsize, Occs ());

  // mark satisfied irredundant clauses as garbage
  for (const auto &c : clauses) {
    if (c->redundant || c->garbage) continue;
    bool satisfied = false;
    unsigned count = 0;
    for (const auto &lit : *c) {
      const signed char tmp = val (lit);
      if (!tmp) count++;
      else if (tmp > 0) {
        satisfied = true;
        break;
      }
    }
    assert (satisfied || count > 1);
    if (satisfied)
      mark_garbage (c); // forces more precise counts
    else if (count == 2) {
      for (const auto &lit : *c) {
        factor.occurs[vlit (lit)].push_back (c);
      }
    }
  }

}

// go back to two watch scheme
void Internal::reset_factor_mode () {
  // reset_occs ();
  // reset_noccs ();
  init_watches ();
  connect_watches ();
}

void Internal::updated_scores_for_new_variables (int64_t added) {
  for (int lit = max_var; added > 0; lit--, added--) {
    bump_variable (lit);
    bump_variable (-lit);
  }
}

void Internal::delete_all_factored (Factorizor &factor) {
  for (auto c : factor.delete_later) {
    assert (c->garbage);
    c->garbage = false;
    mark_garbage (c);
  }
  stats.factor_deleted += factor.delete_later.size ();
  factor.delete_later.clear ();
}

void Internal::try_and_factor (Factorizor &factor, int first, int second) {
  vector<Clause *> current;
  vector<int> &common = factor.common;
  vector<Occs> &occurs = factor.occurs;
  for (auto c : occurs[vlit (second)]) {
    if (!(stats.factor & 1) && c->garbage) continue;
    if (c->garbage) continue;
    int other = 0;
    for (auto lit : *c) {
      if (val (lit) < 0) continue;
      if (lit == second) continue;
      other = lit; 
      break;
    }
    if (marked_signed (other)) {
      current.push_back (c);
      common.push_back (other);
    }
  }
  // actually do factorization
  if (current.size () >= 2) {
    for (auto c : current) {
      if (!c->garbage) {
        factor.delete_later.push_back (c);
        c->garbage = true;
      }
    }
    find_and_delete_outer (factor, first);
    stats.factor_vars++;
    Clause *res;
    int a = external->internalize (external->max_var + 1);
    mark_signed (a);
    factor.occurs.resize (2 *vsize, Occs ());
    if (watching ())
      reset_watches ();
    int b = first;
    int c = second;
    clause.push_back (a);
    clause.push_back (b);
    res = new_factor_clause ();
    factor.occurs[vlit (a)].push_back (res);
    factor.occurs[vlit (b)].push_back (res);
    clause.clear ();
    clause.push_back (a);
    clause.push_back (c);
    res = new_factor_clause ();
    factor.occurs[vlit (a)].push_back (res);
    factor.occurs[vlit (c)].push_back (res);
    clause.clear ();
    auto id = ++clause_id;
    if (proof) {
      clause.push_back (-a);
      clause.push_back (-b);
      clause.push_back (-c);
      proof->add_derived_clause (id, false, clause, lrat_chain);
      clause.clear ();
    }
    for (auto &lit : common) {
      clause.push_back (-a);
      assert (lit != first && lit != second);
      clause.push_back (lit);
      res = new_factor_clause ();
      factor.occurs[vlit (-a)].push_back (res);
      factor.occurs[vlit (lit)].push_back (res);
      clause.clear ();
    }
    if (proof) {
      clause.push_back (-a);
      clause.push_back (-b);
      clause.push_back (-c);
      proof->delete_clause (id, false, clause);
      clause.clear ();
    }
  }
  common.clear ();
}

void Internal::mark_outer (Factorizor &factor, int outer) {
  vector<Occs> &occurs = factor.occurs;
  if (occurs.size () < 2) return;
  for (auto c : occurs[vlit (outer)]) {
    if (!(stats.factor & 1) && c->garbage) continue;
    if (c->garbage) continue;
    int other = 0;
    for (auto lit : *c) {
      if (val (lit) < 0) continue;
      if (lit == outer) continue;
      other = lit; 
      break;
    }
    assert (other);
    if (!marked_signed (other))
      mark_signed (other);
  }
}

void Internal::find_and_delete_outer (Factorizor &factor, int outer) {
  vector<Occs> &occurs = factor.occurs;
  for (auto c : occurs[vlit (outer)]) {
    if (!(stats.factor & 1) && c->garbage) continue;
    if (c->garbage) continue;
    int other = 0;
    for (auto lit : *c) {
      if (val (lit) < 0) continue;
      if (lit == outer) continue;
      other = lit; 
      break;
    }
    assert (other);
    if (std::find (factor.common.begin (), factor.common.end (), other) != factor.common.end ()) {
      c->garbage = true;
      factor.delete_later.push_back (c);
      unmark_signed (other);
    }
  }
}

bool Internal::factor () {
  if (unsat)
    return false;
  if (terminated_asynchronously ())
    return false;
  if (!opts.factor)
    return false;
  if (stats.factor >= opts.factorrounds) return false;
  backtrack ();
  assert (!level);
  // if (stats.factor) return false;
  START_SIMPLIFIER (factor, FACTOR);
  stats.factor++;
  uint64_t factored = stats.factor_vars;
  uint64_t added = stats.factor_added;
  uint64_t deleted = stats.factor_deleted;

  Factorizor factor = Factorizor ();
  factor_mode (factor);
  
  for (int outer = 1; outer < max_var; outer++) {
    mark_outer (factor, outer);
    for (int inner = outer+1; inner <= max_var; inner++) {
      try_and_factor (factor, outer, inner);
      try_and_factor (factor, outer, -inner);
    }
    clear_sign_marked_literals ();
    mark_outer (factor, -outer);
    for (int inner = outer+1; inner <= max_var; inner++) {
      try_and_factor (factor, -outer, inner);
      try_and_factor (factor, -outer, -inner);
    }
    clear_sign_marked_literals ();
  }
  reset_factor_mode ();

  delete_all_factored (factor);
  
  factored = stats.factor_vars - factored;
  added = stats.factor_added - added;
  deleted = stats.factor_deleted - deleted;

  updated_scores_for_new_variables (factored);

  VERBOSE (2, "factored %" PRIu64 " new variables", factored);
  VERBOSE (2, "factorization added %" PRIu64 " and deleted %" PRIu64 " clauses", added, deleted);
  report ('f', !factored);
  STOP_SIMPLIFIER (factor, FACTOR);
  return factored;
}

}