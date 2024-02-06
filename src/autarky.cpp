#include "internal.hpp"
#include <cstdint>

namespace CaDiCaL {

unsigned Internal::autarky_propagate_clause (Clause *c, std::vector<signed char> &autarky_val, std::vector<int> &work) {
  assert (!c->redundant);
  assert (!c->garbage);
  assert (!level);
  bool satisfied = false;
  bool falsified = false;
  unsigned unassigned = 0;
  LOG (c, "autarky checking clause");
  for (auto lit : *c) {
    const int idx = abs (lit);
    if (frozen (idx))
      continue;
    if (val (lit) > 0) {
      LOG ("removing satisfied clause");
      mark_garbage(c);
      return 0;
    }
    if (val (lit) < 0)
      continue;

    const int v = autarky_val[vlit (lit)];
    if (v > 0)
      satisfied = true;
    else if (v < 0)
      falsified = true;
  }

  if (satisfied)
    return 0;
  if (!falsified)
    return 0;
  LOG ("clause is neither satisfied nor falsified, removing all set literals");

  for (auto lit : *c) {
    const int idx = abs (lit);
    if (frozen (idx))
      continue;
    if (val (lit) < 0)
      continue;
    const int v = autarky_val[vlit (lit)];
    if (!v)
      continue;
    assert (v < 0);
    LOG ("unassigning lit %d", lit);
    autarky_val[vlit (idx)] = autarky_val[vlit (-idx)] = 0;
    work.push_back (-lit);
    ++unassigned;
  }
  assert (unassigned);
  return unassigned;
}

unsigned Internal::autarky_propagate_unassigned (std::vector<signed char> &autarky_val, std::vector<int> &work, int lit) {
  int unassigned = 0;
  const Watches &ws = watches (lit);
  for (auto &w : ws) {
    if (w.clause->garbage)
      continue;
    if (w.clause->redundant)
      continue;
    LOG (w.clause, "autarking working on clause");
    unassigned += autarky_propagate_clause(w.clause, autarky_val, work);
  }
  return unassigned;
}

unsigned Internal::autarky_propagate (std::vector<signed char> &autarky_val, std::vector<int> &work) {
  int unassigned = 0;
  while (!work.empty()) {
    const int lit = work.back();
    work.pop_back();
    LOG ("autarky unsetting lit %d", lit);
    unassigned += autarky_propagate_unassigned (autarky_val, work, lit);
  }
  return unassigned;
}


bool Internal::determine_autarky (std::vector<signed char> &autarky_val, std::vector<int> &work) {

  unsigned assigned = 0;
  
  for (auto idx : vars) {
    autarky_val[vlit (idx)] = 0;
    autarky_val[vlit (-idx)] = 0;
    if (!flags (idx).active())
      continue;
    if (frozen (idx))
      continue;
    if (val (idx))
      continue;
    const signed char v = phases.saved[idx];
    LOG ("setting initial value of %d to %d", idx, v);
    autarky_val[vlit (idx)] = v;
    autarky_val[vlit (-idx)] = -v;
    assert (autarky_val[vlit (idx)] == -autarky_val[vlit (-idx)]);
    ++assigned;
  }

  // pre-filtering
  for (auto *c : clauses) {
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;

    const  unsigned unassigned = autarky_propagate_clause(c, autarky_val, work);
    if (!unassigned)
      continue;
    assert (unassigned <= assigned);
    assigned -= unassigned;
    if (!assigned)
      break;
  }

  if (assigned) {
    LOG ("preliminary autarky of size %d", assigned);
  }   else {
    LOG ("empty autarky");
    return false;
  }

  for (auto lit : lits) {
    if (!assigned)
      break;
    if (!flags(lit).active() || frozen (lit))
      continue;
    const signed char v = autarky_val[vlit (lit)];

    if (v > 0)
      continue;
    work.push_back(lit);
    autarky_propagate (autarky_val, work);
  }

  clear_watches();
  // let's not go over the watches like kissat and directly go over the clauses.
  
  for (auto *c : clauses) {
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    LOG (c, "final checking clause for autarky ");
    unsigned unassigned = autarky_propagate_clause (c, autarky_val, work);
    if (unassigned) {
      assigned -= autarky_propagate(autarky_val, work);
    }
    else {
      const int l1 = c->literals[0];
      const int l2 = c->literals[1];
      for (auto lit: *c) {
	const signed char v = autarky_val[vlit (lit)];
	const int other = (lit == l1 ? l2 : l1);
	if (v > 0)
	  watch_literal(lit, other, c);
      }
    }
    // removed: propagate_autarky

  }
  
  clear_watches();

  if (assigned) {
    LOG ("found autarky of size %d", assigned);
  } else {
    LOG ("empty autarky");
    reset_watches();
  }

  return assigned;
}

void Internal::autarky_apply (const std::vector<signed char> &autarky_val,
                              const std::vector<int> &actual_autarky) {

  LOG (actual_autarky, "the autarky is ");
  int removed = 0;
  for (auto *c : clauses) {
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    bool satisfied = false;
    bool falsified = false;
    for (auto lit : *c) {
      const signed char v = autarky_val [vlit (lit)];
      if (v > 0) {
	satisfied = true; break;
      }
      if (v < 0) {
	falsified = true; continue;
      }
    }
    LOG (c, "clause");
    assert (!falsified || satisfied);
    if (satisfied) {
      external->push_zero_on_extension_stack ();
      for (auto lit : actual_autarky)
        external->push_witness_literal_on_extension_stack (lit);
      external->push_clause_on_extension_stack (c);
      LOG (c, "autarky removed satisfied clause");
      mark_garbage(c);
      ++removed;
    }
  }
  LOG ("autarky removed %d clauses", removed);
}

bool Internal::autarky () {
  std::vector<signed char> autarky_val; autarky_val.resize (2*max_var + 1);
  std::vector<int> work;

  int autarky_found = determine_autarky(autarky_val, work);
  if (!autarky_found)
    return false;

  std::vector<int> actual_autarky; actual_autarky.reserve (autarky_found);
  for (auto idx : vars) {
    if (!autarky_val [vlit (idx)])
      continue;
    LOG ("var %d is in the autarky", idx);
    if (autarky_val [vlit (idx)] > 0)
      actual_autarky.push_back(idx);
    else {
      assert (autarky_val [vlit (-idx)] > 0);
      assert (autarky_val [vlit (idx)] < 0);
      actual_autarky.push_back(-idx);
    }
  }

  autarky_apply (autarky_val, actual_autarky);
  
  connect_watches();
  
  return autarky_found;
}

}