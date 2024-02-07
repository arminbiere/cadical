#include "internal.hpp"
#include <cstdint>

namespace CaDiCaL {
// Algorithm to find autarkies based on the phases.  For incremental SAT solving, this can be a
// bootleneck, because the witness for the reconstruction stack can be huge.
inline unsigned Internal::autarky_propagate_clause (Clause *c, std::vector<signed char> &autarky_val, std::vector<int> &work) {
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

unsigned Internal::autarky_propagate_binary (Clause *c, std::vector<signed char> &autarky_val, std::vector<int> &work, int lit) {
  assert (!c->redundant);
  assert (!c->garbage);
  assert (!level);
  (void) c;
  if (val (lit) > 0)
    return 0;
  const int v = autarky_val[vlit (lit)];
  if (v >= 0) {
    return 0;
  }
  assert (v < 0);
  LOG ("unassigning lit %d", lit);
  autarky_val[vlit (lit)] = autarky_val[vlit (-lit)] = 0;
  work.push_back (-lit);
  return 1;
}

unsigned Internal::autarky_propagate_unassigned (std::vector<signed char> &autarky_val, std::vector<int> &work, int lit) {
  int unassigned = 0;
  assert (autarky_val[vlit (lit)] <= 0);
  const Watches &ws = watches (lit);
  for (auto &w : ws) {
    if (w.clause->garbage)
      continue;
    if (w.clause->redundant)
      continue;
    LOG (w.clause, "autarking working on clause");
    if (w.binary()){
      unassigned += autarky_propagate_binary (w.clause, autarky_val, work, w.blit);
    }
    else
      unassigned += autarky_propagate_clause (w.clause, autarky_val, work);
  }
  return unassigned;
}

unsigned Internal::autarky_propagate (std::vector<signed char> &autarky_val, std::vector<int> &work) {
  int unassigned = 0;
  while (!work.empty()) {
    const int lit = work.back();
    work.pop_back();
    LOG ("autarky propagating lit %d (%d unassigned)", lit, unassigned);
    unassigned += autarky_propagate_unassigned (autarky_val, work, lit);
  }
  return unassigned;
}


int Internal::determine_autarky (std::vector<signed char> &autarky_val, std::vector<int> &work) {
  unsigned assigned = 0;
  // importing phases
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

#ifndef NDEBUG
  {
    unsigned i = 0;
    for (auto lit : vars) {
      if (autarky_val[vlit (lit)])
        ++i;
    }
    assert (i == assigned);
  }
#endif

  // pre-filtering
  for (auto *c : clauses) {
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;

    const unsigned unassigned = autarky_propagate_clause(c, autarky_val, work);
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

#ifndef NDEBUG
  {
    unsigned i = 0;
    for (auto lit : vars) {
      if (autarky_val[vlit (lit)])
        ++i;
    }
    assert (i == assigned);
  }
#endif

  for (auto lit : lits) {
    if (!assigned)
      break;
    if (!flags(lit).active() || frozen (lit))
      continue;
    const signed char v = autarky_val[vlit (lit)];

    if (v > 0)
      continue;
    work.push_back(lit);
    assigned -= autarky_propagate (autarky_val, work);
  }

#ifndef NDEBUG
  {
    unsigned i = 0;
    for (auto lit : vars) {
      if (autarky_val[vlit (lit)])
        ++i;
    }
    assert (i == assigned);
  }
#endif

  // final pass. This requires a one-watch literal scheme.
  clear_watches();
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
    connect_watches ();
  }

  return assigned;
}

void Internal::autarky_apply (const std::vector<signed char> &autarky_val,
                              const std::vector<int> &actual_autarky) {

  int removed = 0;
  bool compact = opts.autarkynonincr;
  if (!compact)
    LOG (actual_autarky, "the autarky is ");

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
      if (!compact) {
        external->push_zero_on_extension_stack ();
        for (auto lit : actual_autarky)
          external->push_witness_literal_on_extension_stack (lit);
        external->push_clause_on_extension_stack (c);
      }
      LOG (c, "autarky removed satisfied clause");
      mark_garbage (c);
      ++removed;
    }
  }

  if (compact) {
    for (auto lit : lits) {
      const signed char v = autarky_val [vlit (lit)];
      if (v > 0) {
        external->push_zero_on_extension_stack ();
        external->push_witness_literal_on_extension_stack (lit);
	external->push_id_on_extension_stack (lit); //fake id
        external->push_zero_on_extension_stack ();
        external->push_clause_literal_on_extension_stack (lit);
        external->push_zero_on_extension_stack ();
      }
    }
  }
  LOG ("autarky removed %d clauses", removed);
}

bool Internal::autarky () {
  assert (!level);
  if (!opts.autarkies)
    return false;
  START (autarky);

  printf ("allocating %d\n", 2*max_var + 1);
  std::vector<signed char> autarky_val; autarky_val.resize (2*max_var + 1);
  std::vector<int> work;

  ++stats.autarkies.tries;
  int autarky_found = determine_autarky(autarky_val, work);
  if (!autarky_found){
    STOP (autarky);
    return false;
  }

  std::vector<int> actual_autarky; actual_autarky.reserve (autarky_found);
  const bool full_aut = !opts.autarkynonincr;

  for (auto idx : vars) {
    if (!autarky_val [vlit (idx)])
      continue;
    assert (active (idx));
    if (autarky_val [vlit (idx)] > 0){
      if (full_aut) actual_autarky.push_back(idx);
      mark_eliminated (idx);
    }
    else {
      assert (autarky_val [vlit (-idx)] > 0);
      assert (autarky_val [vlit (idx)] < 0);
      if (full_aut) actual_autarky.push_back(-idx);
      mark_eliminated (idx);
    }
  }

  autarky_apply (autarky_val, actual_autarky);

  ++stats.autarkies.rounds;
  stats.autarkies.eliminated += autarky_found;
  mark_redundant_clauses_with_eliminated_variables_as_garbage ();
  connect_watches();
  report ('a');
  STOP (autarky);
  return autarky_found;
}

}