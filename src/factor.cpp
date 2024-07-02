#include "internal.hpp"

namespace CaDiCaL {

// essentially do full occurence list as in elim.cpp
void Internal::factor_mode () {
  reset_watches ();

  assert (!watching ());
  init_noccs ();
  init_occs ();

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
        noccs (lit)++;  
        occs (lit).push_back (c);
      }
    }
  }

}

// go back to two watch scheme
void Internal::reset_factor_mode () {
  reset_occs ();
  reset_noccs ();
  init_watches ();
  connect_watches ();
}

void Internal::updated_scores_for_new_variables (int64_t added) {
  for (int lit = max_var; added > 0; lit--, added--)
    bump_variable (lit);
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
  vector<int> common;
  for (auto c : occs (second)) {
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
  if (current.size () >= 3) {
    for (auto c : current) {
      if (!c->garbage) {
        factor.delete_later.push_back (c);
        c->garbage = true;
      }
    }
    stats.factor_vars++;
    int a = external->internalize (external->max_var + 1);
    if (watching ())
      reset_watches ();
    int b = first;
    int c = second;
    clause.push_back (a);
    clause.push_back (b);
    new_factor_clause ();
    clause.clear ();
    clause.push_back (a);
    clause.push_back (c);
    new_factor_clause ();
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
      new_factor_clause ();
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
}

void Internal::mark_outer (int outer) {
  if (noccs (outer) < 3) return;
  for (auto c : occs (outer)) {
    if (c->garbage) continue;
    int other = 0;
    for (auto lit : *c) {
      if (val (lit) < 0) continue;
      if (lit == outer) continue;
      other = lit; 
      break;
    }
    assert (other);
    mark_signed (other);
  }
}


bool Internal::factor () {
  if (unsat)
    return false;
  if (terminated_asynchronously ())
    return false;
  if (!opts.factor)
    return false;
  assert (!level);
  // if (stats.factor) return false;
  START_SIMPLIFIER (factor, FACTOR);
  stats.factor++;
  uint64_t factored = stats.factor_vars;
  uint64_t added = stats.factor_added;
  uint64_t deleted = stats.factor_deleted;

  factor_mode ();
  Factorizor factor = Factorizor ();
  
  int old_max_var = max_var;
  for (int outer = 1; outer < old_max_var; outer++) {
    mark_outer (outer);
    for (int inner = outer+1; inner <= old_max_var; inner++) {
      try_and_factor (factor, outer, inner);
      try_and_factor (factor, outer, -inner);
    }
    clear_sign_marked_literals ();
    mark_outer (-outer);
    for (int inner = outer+1; inner <= old_max_var; inner++) {
      try_and_factor (factor, -outer, inner);
      try_and_factor (factor, -outer, -inner);
    }
    clear_sign_marked_literals ();
  }
  reset_factor_mode ();

  delete_all_factored (factor);
  updated_scores_for_new_variables (factored);
  

  factored = stats.factor_vars - factored;
  added = stats.factor_added - added;
  deleted = stats.factor_deleted - deleted;
  VERBOSE (2, "factored %" PRIu64 " new variables", factored);
  VERBOSE (2, "factorization added %" PRIu64 " and deleted %" PRIu64 " clauses", added, deleted);
  report ('f', factored);
  STOP_SIMPLIFIER (factor, FACTOR);
  return factored;
}

}