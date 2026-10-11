#include "internal.hpp"

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
    else if (v < 0) {
      falsified = true;
    }
  }

  if (satisfied)
    return 0;
  if (!falsified)
    return 0;
  LOG ("clause is falsified and not satisfied, removing all set literals");

  for (auto lit : *c) {
    if (frozen (lit))
      continue;
    if (val (lit) < 0)
      continue;
    const int v = autarky_val[vlit (lit)];
    if (!v)
      continue;
    assert (v < 0);
    LOG ("unassigning lit %d", lit);
    autarky_val[vlit (lit)] = autarky_val[vlit (-lit)] = 0;
    work.push_back (-lit);

    ++unassigned;
  }
  assert (unassigned);
  return unassigned;
}

unsigned Internal::autarky_propagate_binary (Clause *c, std::vector<signed char> &autarky_val, std::vector<int> &work, int lit) {
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
    if (w.binary()) {
        unassigned += autarky_propagate_binary (w.clause, autarky_val, work, w.blit);
    }
    else
      unassigned += autarky_propagate_clause (w.clause, autarky_val, work);
  }
  return unassigned;
}

unsigned Internal::autarky_propagate_unassigned_binary (std::vector<signed char> &autarky_val, std::vector<int> &work, int lit) {
  int unassigned = 0;
  assert (autarky_val[vlit (lit)] <= 0);
  const Watches &ws = watches (lit);
  for (auto &w : ws) {
    // if (w.clause->garbage)
    //   continue;
    // if (w.clause->redundant)
    //   continue;
    LOG (w.clause, "autarking working on clause");
    if (w.binary()){
        unassigned += autarky_propagate_binary (w.clause, autarky_val, work, w.blit);
    }
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
  const bool target = false && (opts.target > 1 || (stable && opts.target));
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
    signed char v = target ? phases.target[idx] : phases.saved[idx];
    if (!v)
      v = opts.phase ? 1 : -1;
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
    if (last_irredundant && c > last_irredundant)
      break;
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
  } else {
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
    // first just do the binary watches for speed
    assigned -= autarky_propagate_unassigned_binary (autarky_val, work, lit);
    //work.push_back(lit);
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

  if (assigned) {
    LOG ("second stage autarky of size %d", assigned);
  }   else {
    LOG ("empty autarky");
    return false;
  }

  // final pass. This requires a full-watched literal scheme.
  clear_watches ();
  for (auto *c : clauses) {
    if (!assigned)
      break;
    if (last_irredundant && c > last_irredundant)
      break;
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    LOG (c, "final checking clause for autarky ");
    unsigned unassigned = autarky_propagate_clause (c, autarky_val, work);
    if (unassigned) {
      assigned -= unassigned + autarky_propagate(autarky_val, work);
    }
    else {
      const int l1 = c->literals[0];
      const int l2 = c->literals[1];
      for (auto lit: *c) {
        const signed char v = autarky_val[vlit (lit)];
        const int other = (lit == l1 ? l2 : l1);
        if (v > 0) {
          Watches &ws = watches (lit);
          ws.push_back (Watch (other, c));
          LOG (c, "watch %d blit %d in", lit, other);
        }
      }
    }
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

  if (assigned) {
    LOG ("found autarky of size %d", assigned);
  } else {
    LOG ("empty autarky");
  }
  clear_watches ();
  connect_watches ();
  return assigned;
}

void Internal::autarky_apply (const std::vector<signed char> &autarky_val,
                              const std::vector<int> &actual_autarky) {

  int removed = 0;
  bool compact = opts.autarkynonincr;
  LOG (actual_autarky, "the autarky is ");

  for (auto *c : clauses) {
    if (c->garbage)
      continue;
#ifndef NDEBUG
    bool satisfied = false;
    bool falsified = false;
#endif
    bool touched = false;
    for (auto lit : *c) {
      const signed char v = autarky_val [vlit (lit)];
      touched = (touched || v);
#ifndef NDEBUG
      if (v > 0) {
        satisfied = true; break;
      }
      if (v < 0) {
        falsified = true;
        continue;
      }
#endif
    if (v)
      break;
    }
    LOG (c, "clause");
    assert (c->redundant || !falsified || satisfied);
    assert (c->redundant || touched == satisfied);
    if (c->redundant && touched) {
      LOG (c, "delete touched clause");
      mark_garbage (c);
      continue;
    }
    if (touched) {
      assert (!c->redundant);
      if (!compact) {
        if (proof)
          proof->weaken_minus(c);
        std::vector<int> witness = actual_autarky;
        external->push_external_clause_and_witness_on_extension_stack(c, std::move (witness));
      }
      LOG (c, "autarky removed satisfied clause");
      mark_garbage (c);
      ++removed;
    }
  }
  // the clause to ignore are marked garbage, but we need to delete
  // binary clauses explicitely.
  for (auto lit : lits) {
    const signed char v = autarky_val[vlit (lit)];
    if (v) {
      watches (lit).clear ();
      continue;
    }
    auto begin = watches (lit).begin ();
    auto i = begin;
    auto end = watches (lit).end ();
    for (auto j = i; j < end;) {
      assert (i <= j);
      Watch w = (*i++ = *j++);
      if (w.binary () && autarky_val[vlit (w.blit)]) {
        --i;
      }
    }
    if (i != end) {
      watches (lit).resize (i - begin);
    }
  }
  MSG ("autarky applied");
  if (compact) {
    for (auto var : vars) {
      const signed char v = autarky_val [vlit (var)];
      if (!v)
        continue;
      assert (v == 1 || v == -1);
      int lit = v * var;
      // fake id!
      external->push_external_clause_and_witness_on_extension_stack({lit}, {lit}, var);
    }
  }

  LOG ("autarky removed %d clauses", removed);
}

bool Internal::autarky (char c) {
  if (unsat)
    return false;
  if (level) // conflict during warmup
    return false;
  if (!opts.autarkies)
    return false;
  if (delay->bumpreasons.interval > 10){
    delay->bumpreasons.limit = 0;
    delay->bumpreasons.interval = 10;
  }
  if (opts.autarkydelay && delay_autarky.bumpreasons.delay ()) {
     delay_autarky.bumpreasons.reduce_delay ();
     return false;
  }
  START (autarky);
  START (autarkydetermine);

  std::vector<signed char> autarky_val; autarky_val.resize (2*max_var + 2);
  std::vector<int> work;

  ++stats.autarkies.tries;
  int autarky_found = determine_autarky(autarky_val, work);
  if (!autarky_found){
    delay_autarky.bumpreasons.bump_delay ();
    STOP (autarkydetermine);
    STOP (autarky);
    return false;
  }
  delay_autarky.bumpreasons.reduce_delay ();
  std::vector<int> actual_autarky; actual_autarky.reserve (autarky_found);
  const bool full_aut = !opts.autarkynonincr;

  STOP (autarkydetermine);
  START (autarkyapply);
  for (auto idx : vars) {
    if (!active (idx))
      continue;
    if (!autarky_val [vlit (idx)])
      continue;
    assert (active (idx));
    if (autarky_val [vlit (idx)] > 0){
      if (full_aut) actual_autarky.push_back(idx);
    }
    else {
      assert (autarky_val [vlit (-idx)] > 0);
      assert (autarky_val [vlit (idx)] < 0);
      if (full_aut) actual_autarky.push_back(-idx);
    }
  }
  assert (!full_aut || !actual_autarky.empty ());

  autarky_apply (autarky_val, actual_autarky);


  for (auto idx : vars) {
    if (!autarky_val [vlit (idx)])
      continue;
    assert (active (idx));
    mark_eliminated (idx);
  }
  STOP (autarkyapply);
  ++stats.autarkies.successful;
  stats.autarkies.eliminated += autarky_found;
  //mark_redundant_clauses_with_eliminated_variables_as_garbage ();
  report (c);
  STOP (autarky);
  return autarky_found;
}

}
