#include "internal.hpp"

namespace CaDiCaL {

Sweeper::Sweeper (Internal *i) : internal (i),
                                      random (internal->opts.seed) {
  random += internal->stats.sweep; // different seed every time
  internal->init_sweeper (*this);
}

Sweeper::~Sweeper () {
  // this is already called actively
  // internal->release_sweeper (this);
  return;
}

int Internal::sweep_solve () {
  kitten_randomize_phases (citten);
  stats.sweep_solved++;
  int res = kitten_solve (citten);
  if (res == 10)
    stats.sweep_sat++;
  if (res == 20)
    stats.sweep_unsat++;
  return res;
}

void Internal::sweep_set_kitten_ticks_limit (Sweeper &sweeper) {
  uint64_t remaining = 0;
  const uint64_t current = kitten_current_ticks (citten);
  if (current < sweeper.limit.ticks)
    remaining = sweeper.limit.ticks - current;
  LOG ("'kitten_ticks' remaining %" PRIu64, remaining);
  kitten_set_ticks_limit (citten, remaining);
}

// essentially do full occurence list as in elim.cpp
void Internal::sweep_dense_mode_and_watch_irredundant () {
  reset_watches ();

  // mark satisfied irredundant clauses as garbage
  for (const auto &c : clauses) {
    if (c->garbage || c->redundant)
      continue;
    bool satisfied = false;
    for (const auto &lit : *c) {
      const signed char tmp = val (lit);
      if (tmp <= 0) continue;
      if (tmp > 0) {
        satisfied = true;
        break;
      }
    }
    if (satisfied)
      mark_garbage (c); // forces more precise counts
  }

  init_occs ();

  // Connect irredundant clauses.
  //
  for (const auto &c : clauses)
    if (!c->garbage && !c->redundant)
      for (const auto &lit : *c)
        if (active (lit))
          occs (lit).push_back (c);
}

// go back to two watch scheme
void Internal::sweep_sparse_mode () {
  reset_occs ();
  init_watches ();
  connect_watches ();
}

// propagate without watches but full occurence list
void Internal::sweep_dense_propagate (Sweeper &sweeper) {
  vector<int> &work = sweeper.propagate;
  size_t i = 0;
  while (i < work.size ()) {
    int lit = work[i++];
    LOG ("sweeping propagation of %d", lit);
    assert (val (lit) > 0);
    const Occs &ns = occs (-lit);
    for (const auto &c : ns) {
      if (c->garbage)
        continue;
      int unit = 0, satisfied = 0;
      for (const auto &other : *c) {
        const signed char tmp = val (other);
        if (tmp < 0)
          continue;
        if (tmp > 0) {
          satisfied = other;
          break;
        }
        if (unit)
          unit = INT_MIN;
        else
          unit = other;
      }
      if (satisfied) {
        LOG (c, "sweeping propagation of %d finds %d satisfied", lit,
             satisfied);
        mark_garbage (c);
      } else if (!unit) {
        LOG ("empty clause during sweeping propagation of %d", lit);
        // need to set conflict = c for lrat
        conflict = c;
        learn_empty_clause ();
        conflict = 0;
        break;
      } else if (unit != INT_MIN) {
        LOG ("new unit %d during sweeping propagation of %d", unit, lit);
        build_chain_for_units (unit, c, 0);
        assign_unit (unit);
        work.push_back (unit);
      }
    }
    if (unsat)
      break;
    
    // TODO might not be necessary
    const Occs &ps = occs (lit);
    for (const auto &c : ps) {
      if (c->garbage)
        continue;
      LOG (c, "sweeping propagation of %d produces satisfied", lit);
      mark_garbage (c);
    }
  }
  work.clear ();
}

bool Internal::kitten_ticks_limit_hit (Sweeper &sweeper, const char *when) {
  const uint64_t current = kitten_current_ticks (citten);
  if (current >= sweeper.limit.ticks) {
    LOG ("'kitten_ticks' limit of %" PRIu64 " ticks hit after %" PRIu64
         " ticks during %s",
         sweeper.limit.ticks, current, when);
    return true;
  }
#ifndef LOGGING
  (void) when;
#endif
  return false;
}


void Internal::init_sweeper (Sweeper &sweeper) {
  sweeper.encoded = 0;
  enlarge_zero (sweeper.depths, max_var + 1);
  sweeper.reprs = new int[2 * max_var + 1];
  sweeper.reprs -= max_var;
  enlarge_zero (sweeper.prev, max_var + 1);
  enlarge_zero (sweeper.next, max_var + 1);
  for (const auto & lit : lits)
    sweeper.reprs[lit] = lit;
  sweeper.first = sweeper.last = 0;
  assert (!citten);
  citten = kitten_init ();
  kitten_track_antecedents (citten);

  sweep_dense_mode_and_watch_irredundant (); // full occurence list

  unsigned completed = stats.sweep_completed;
  const unsigned max_completed = 32;
  if (completed > max_completed)
    completed = max_completed;

  uint64_t vars_limit = opts.sweepvars;
  vars_limit <<= completed;
  const unsigned max_vars_limit = opts.sweepmaxvars;
  if (vars_limit > max_vars_limit)
    vars_limit = max_vars_limit;
  sweeper.limit.vars = vars_limit;
  VERBOSE (3, "sweeper variable limit %u",
                            sweeper.limit.vars);

  uint64_t depth_limit = stats.sweep_completed;
  depth_limit += opts.sweepdepth;
  const unsigned max_depth = opts.sweepmaxdepth;
  if (depth_limit > max_depth)
    depth_limit = max_depth;
  sweeper.limit.depth = depth_limit;
  VERBOSE (3, "sweeper depth limit %u",
                            sweeper.limit.depth);

  uint64_t clause_limit = opts.sweepclauses;
  clause_limit <<= completed;
  const unsigned max_clause_limit = opts.sweepmaxclauses;
  if (clause_limit > max_clause_limit)
    clause_limit = max_clause_limit;
  sweeper.limit.clauses = clause_limit;
  VERBOSE (3, "sweeper clause limit %u",
                            sweeper.limit.clauses);

  if (opts.sweepcomplete) {
    sweeper.limit.ticks = UINT64_MAX;
    VERBOSE (3, "unlimited sweeper ticks limit");
  } else {
    int64_t limit = stats.propagations.search;
    limit -= last.sweep.propagations;
    limit *= opts.sweepeffort * 1e-3;
    // if (limit < opts.sweepmineff)  TODO maybe these options
    //   limit = opts.sweepmineff;        
    // if (limit > opts.sweepmaxeff)
    //   limit = opts.sweepmaxeff;
    int64_t ticks_limit = limit * 100;   // propagations are not equal ticks
    sweeper.limit.ticks = ticks_limit;
    last.sweep.propagations = stats.propagations.search;
  }
  sweep_set_kitten_ticks_limit (sweeper);
}

unsigned Internal::release_sweeper (Sweeper &sweeper) {

  unsigned merged = 0;
  for (const auto & idx : vars) {
    if (!active (idx))
      continue;
    const int lit = idx;
    if (sweeper.reprs[lit] != lit)
      merged++;
  }
  sweeper.reprs += max_var;
  delete[] sweeper.reprs;
  
  erase_vector (sweeper.depths);
  erase_vector (sweeper.prev);
  erase_vector (sweeper.next);
  erase_vector (sweeper.vars);
  erase_vector (sweeper.clause);
  erase_vector (sweeper.backbone);
  erase_vector (sweeper.partition);
  for (unsigned i = 0; i < 2; i++)
    erase_vector (sweeper.core[i]);
  
  kitten_release (citten);
  citten = 0;
  sweep_sparse_mode ();
  return merged;
}

void Internal::clear_sweeper (Sweeper &sweeper) {
  LOG ("clearing sweeping environment");
  kitten_clear (citten);
  kitten_track_antecedents (citten);
  for (auto & idx : sweeper.vars) {
    assert (sweeper.depths[idx]);
    sweeper.depths[idx] = 0;
  }
  sweeper.vars.clear ();
  for (auto c : sweeper.clauses) {
    assert (c->swept);
    c->swept = false;
  }
  sweeper.clauses.clear ();
  sweeper.backbone.clear ();
  sweeper.partition.clear ();
  sweeper.encoded = 0;
  sweep_set_kitten_ticks_limit (sweeper);
}

int Internal::sweep_repr (Sweeper &sweeper, int lit) {
  int res;
  {
    int prev = lit;
    while ((res = sweeper.reprs[prev]) != prev)
      prev = res;
  }
  if (res == lit)
    return res;
  LOG ("sweeping repr[%d] = %d", lit, res);
  {
    const int not_res = -res;
    int next, prev = lit;
    while ((next = sweeper.reprs[prev]) != res) {
      const int not_prev = -prev;
      sweeper.reprs[not_prev] = not_res;
      sweeper.reprs[prev] = res;
      prev = next;
    }
    assert (sweeper.reprs[-prev] == not_res);
  }
  return res;
}

void Internal::add_literal_to_environment (Sweeper &sweeper, unsigned depth,
                                        int lit) {
  const int repr = sweep_repr (sweeper, lit);
  if (repr != lit)
    return;
  const int idx = abs (lit);
  if (sweeper.depths[idx])
    return;
  assert (depth < UINT_MAX);
  sweeper.depths[idx] = depth + 1;
  sweeper.vars.push_back (idx);
  LOG ("sweeping[%u] adding literal %d", depth, lit);
}

void Internal::sweep_add_clause (Sweeper &sweeper, unsigned depth) {
  assert (sweeper.clause.size () > 1);
  for (const auto & lit : sweeper.clause)
    add_literal_to_environment (sweeper, depth, lit);
  citten_clause (citten, sweeper.clause.size (), sweeper.clause.data ());
  sweeper.clause.clear ();
  sweeper.encoded++;
}

void Internal::sweep_clause (Sweeper &sweeper, unsigned depth, Clause *c) {
  if (c->swept)
    return;
  if (c->garbage)
    return;
  LOG (c, "sweeping[%u]", depth);
  assert (sweeper.clause.empty ());
  for (const auto & lit : *c) {
    const signed char tmp = val (lit);
    if (tmp > 0) {
      mark_garbage (c);
      return;
    }
    if (tmp < 0)
      continue;
    sweeper.clause.push_back (lit);
  }
  sweeper.clauses.push_back (c);
  c->swept = true;
  sweep_add_clause (sweeper, depth);
}


extern "C" {
static void save_core_clause (void *state, bool learned, size_t size,
                              const unsigned *lits) {
  Sweeper *sweeper = (Sweeper *) state;
  Internal *internal = sweeper->internal;
  if (internal->unsat)
    return;
  // TODO proof clause or int
  vector<int> &core = sweeper->core[sweeper->save];
  size_t saved = core.size ();
  const unsigned *end = lits + size;
  unsigned non_false = 0;
  for (const unsigned *p = lits; p != end; p++) {
    const unsigned ulit = *p;
    const int lit = internal->citten2lit (ulit);
    const signed char tmp = internal->val (lit);
    if (tmp > 0) {
      LOG (size, lits, "extracted %d satisfied lemma", LOG (lit));
      core.resize (saved);
      return;
    }
    core.push_back (lit);
    if (tmp < 0)
      continue;
    if (!learned && ++non_false > 1) {
      // LOGLITS (size, lits, "ignoring extracted original clause");
      core.resize (saved);
      return;
    }
  }
  /*
#ifdef LOGGING
  unsigned *saved_lits = BEGIN_STACK (*core) + saved;
  size_t saved_size = SIZE_STACK (*core) - saved;
  LOGLITS (saved_size, saved_lits, "saved core[%u]", sweeper.save);
#endif
*/
  core.push_back (0);
}
} // end extern C

void Internal::add_core (Sweeper &sweeper, unsigned core_idx) {
  if (unsat)
    return;
  LOG ("check and add extracted core[%u] lemmas to proof", core_idx);
  assert (core_idx == 0 || core_idx == 1);
  vector<int> &core = sweeper.core[core_idx];

  auto q = core.begin (), p = q;
  const auto end_core = core.end ();

  while (p != end_core) {
    auto c = p;
    while (*p != 0)
      p++;
/*
#ifdef LOGGING
    size_t old_size = p - c;
    LOGLITS (old_size, c, "simplifying extracted core[%u] lemma", core_idx);
#endif
*/
    bool satisfied = false;
    int unit = 0;

    auto d = q;

    for (auto l = c; !satisfied && l != p; l++) {
      const int lit = *l;
      const signed char value = val (lit);
      if (value > 0) {
        satisfied = true;
        break;
      }
      if (!value)
        unit = *q++ = lit;
    }

    size_t new_size = q - d;
    p++;

    if (satisfied) {
      q = d;
      LOG ("not adding satisfied clause");
      continue;
    }

    if (!new_size) {
      LOG ("sweeping produced empty clause");
      /*
      CHECK_AND_ADD_EMPTY ();
      ADD_EMPTY_TO_PROOF ();
      */
      learn_empty_clause ();
      core.clear ();
      return;
    }

    if (new_size == 1) {
      q = d;
      assert (unit != 0);
      LOG ("sweeping produced unit %d", unit);
      /*
      CHECK_AND_ADD_UNIT (unit);
      ADD_UNIT_TO_PROOF (unit);
      kissat_assign_unit (solver, unit, "sweeping backbone reason");
      */
      assign_unit (unit);
      sweeper.propagate.push_back (unit);
      stats.sweep_units++;
      continue;
    }

    *q++ = 0;

    assert (new_size > 1);
    /*
    LOGLITS (new_size, d, "adding extracted core[%u] lemma", core_idx);
    CHECK_AND_ADD_LITS (new_size, d);
    ADD_LITS_TO_PROOF (new_size, d);
    */
  }
  core.resize (q - core.begin ());
}

void Internal::save_core (Sweeper &sweeper, unsigned core) {
  LOG ("saving extracted core[%u] lemmas", core);
  assert (core == 0 || core == 1);
  assert (sweeper.core[core].empty ());
  sweeper.save = core;
  kitten_compute_clausal_core (citten, 0);
  kitten_traverse_core_clauses (citten, &sweeper, save_core_clause);
}

void Internal::clear_core (Sweeper &sweeper, unsigned core_idx) {
  if (unsat)
    return;
  assert (core_idx == 0 || core_idx == 1);
  LOG ("clearing core[%u] lemmas", core_idx);
  vector<int> &core = sweeper.core[core_idx];
    /*  TODO core has to store ids (see proof_clauses in definition.cpp/elim.hpp)
  if (proof) {
    LOG ("deleting sub-solver core clauses");
    const unsigned *const end = END_STACK (*core);
    const unsigned *c = BEGIN_STACK (*core);
    for (const unsigned *p = c; c != end; c = ++p) {
      while (*p != INVALID_LIT)
        p++;
      const size_t size = p - c;
      assert (size > 1);
      REMOVE_CHECKER_LITS (size, c);
      DELETE_LITS_FROM_PROOF (size, c);
    }
  }
      */
  core.clear ();
}

void Internal::save_add_clear_core (Sweeper &sweeper) {
  save_core (sweeper, 0);
  add_core (sweeper, 0);
  clear_core (sweeper, 0);
}

/* TODO: logging
#define LOGBACKBONE(MESSAGE) \
  LOGLITSET (SIZE_STACK (sweeper.backbone), \
             BEGIN_STACK (sweeper.backbone), MESSAGE)

#define LOGPARTITION(MESSAGE) \
  LOGLITPART (SIZE_STACK (sweeper.partition), \
              BEGIN_STACK (sweeper.partition), MESSAGE)
*/

              
void Internal::init_backbone_and_partition (Sweeper &sweeper) {
  LOG ("initializing backbone and equivalent literals candidates");
  for (const auto & idx : sweeper.vars) {
    if (!active (idx))
      continue;
    assert (idx > 0);
    const int lit = idx;
    const int not_lit = -lit;
    const signed char tmp = kitten_signed_value (citten, lit);
    const int candidate = (tmp < 0) ? not_lit : lit;
    LOG ("sweeping candidate %d", candidate);
    sweeper.backbone.push_back (candidate);
    sweeper.partition.push_back (candidate);
  }
  sweeper.partition.push_back (0);

  // LOGBACKBONE ("initialized backbone candidates");
  // LOGPARTITION ("initialized equivalence candidates");
}

void Internal::sweep_empty_clause (Sweeper &sweeper) {
  assert (!unsat);
  save_add_clear_core (sweeper);
  assert (unsat);
}

void Internal::sweep_refine_partition (Sweeper &sweeper) {
  LOG ("refining partition");
  vector<int> &old_partition = sweeper.partition;
  vector<int> new_partition;
  auto old_begin = old_partition.begin ();
  const auto old_end = old_partition.end ();
#ifdef LOGGING
  unsigned old_classes = 0;
  unsigned new_classes = 0;
#endif
  for (auto p = old_begin, q = p; p != old_end; p = q + 1) {
    unsigned assigned_true = 0;
    int other;
    for (q = p; (other = *q) != 0; q++) {
      if (sweep_repr (sweeper, other) != other)
        continue;
      if (val (other))
        continue;
      signed char value = kitten_signed_value (citten, other);
      if (!value)
        LOG ("dropping sub-solver unassigned %d", other);
      else if (value > 0) {
        new_partition.push_back (other);
        assigned_true++;
      }
    }
#ifdef LOGGING
    LOG ("refining class %u of size %zu", old_classes, (size_t) (q - p));
    old_classes++;
#endif
    if (assigned_true == 0)
      LOG ("no positive literal in class");
    else if (assigned_true == 1) {
#ifdef LOGGING
      other =
#else
      (void)
#endif
          new_partition.back ();
          new_partition.pop_back ();
      LOG ("dropping singleton class %d", other);
    } else {
      LOG ("%u positive literal in class", assigned_true);
      new_partition.push_back (0);
#ifdef LOGGING
      new_classes++;
#endif
    }

    unsigned assigned_false = 0;
    for (q = p; (other = *q) != 0; q++) {
      if (sweep_repr (sweeper, other) != other)
        continue;
      if (val (other))
        continue;
      signed char value = kitten_signed_value (citten, other);
      if (value < 0) {
        new_partition.push_back (other);
        assigned_false++;
      }
    }

    if (assigned_false == 0)
      LOG ("no negative literal in class");
    else if (assigned_false == 1) {
#ifdef LOGGING
      other =
#else
      (void)
#endif
          new_partition.back ();
          new_partition.pop_back ();
      LOG ("dropping singleton class %d", other);
    } else {
      LOG ("%u negative literal in class", assigned_false);
      new_partition.push_back (0);
#ifdef LOGGING
      new_classes++;
#endif
    }
  }
  old_partition.swap (new_partition);
  LOG ("refined %u classes into %u", old_classes, new_classes);
  // LOGPARTITION ("refined equivalence candidates");
}

void Internal::sweep_refine_backbone (Sweeper &sweeper) {
  LOG ("refining backbone candidates");
  const auto end = sweeper.backbone.end ();
  auto q = sweeper.backbone.begin ();
  for (auto p = q; p != end; p++) {
    const int lit = *p;
    if (val (lit))
      continue;
    signed char value = kitten_signed_value (citten, lit);
    if (!value)
      LOG ("dropping sub-solver unassigned %d", lit);
    else if (value >= 0)
      *q++ = lit;
  }
  sweeper.backbone.resize (q - sweeper.backbone.begin ());
  // LOGBACKBONE ("refined backbone candidates");
}

void Internal::sweep_refine (Sweeper &sweeper) {
  if (sweeper.backbone.empty ())
    LOG ("no need to refine empty backbone candidates");
  else
    sweep_refine_backbone (sweeper);
  if (sweeper.partition.empty ())
    LOG ("no need to refine empty partition candidates");
  else
    sweep_refine_partition (sweeper);
}

void Internal::flip_backbone_literals (Sweeper &sweeper) {
  const unsigned max_rounds = opts.sweepfliprounds;
  if (!max_rounds)
    return;
  assert (sweeper.backbone.size ());
  if (kitten_status (citten) != 10)
    return;
#ifdef LOGGING
  unsigned total_flipped = 0;
#endif
  unsigned flipped, round = 0;
  do {
    round++;
    flipped = 0;
    auto begin = sweeper.backbone.begin (), q = begin, p = q;
    const auto end = sweeper.backbone.end ();
    while (p != end) {
      const int lit = *p++;
      stats.sweep_flip_backbone++;
      if (kitten_flip_signed_literal (citten, lit)) {
        LOG ("flipping backbone candidate %d succeeded", lit);
#ifdef LOGGING
        total_flipped++;
#endif
        stats.sweep_flipped_backbone++;
        flipped++;
      } else {
        LOG ("flipping backbone candidate %d failed", lit);
        *q++ = lit;
      }
    }
    sweeper.backbone.resize (q - sweeper.backbone.begin ());
    LOG ("flipped %u backbone candidates in round %u", flipped, round);

    if (terminated_asynchronously ())
      break;
    if (kitten_current_ticks (citten) > sweeper.limit.ticks)
      break;
  } while (flipped && round < max_rounds);
  LOG ("flipped %u backbone candidates in total in %u rounds",
       total_flipped, round);
}

bool Internal::sweep_backbone_candidate (Sweeper &sweeper, int lit) {
  LOG ("trying backbone candidate %d", lit);
  signed char value = kitten_fixed_signed (citten, lit);
  if (value) {
    stats.sweep_fixed_backbone++;
    LOG ("literal %d already fixed", lit);
    assert (value > 0);
    return false;
  }

  stats.sweep_flip_backbone++;
  if (kitten_status (citten) == 10 && kitten_flip_signed_literal (citten, lit)) {
    stats.sweep_flipped_backbone++;
    LOG ("flipping %d succeeded", lit);
    // LOGBACKBONE ("refined backbone candidates");
    return false;
  }

  LOG ("flipping %d failed", lit);
  const int not_lit = -lit;
  stats.sweep_solved_backbone++;
  kitten_assume_signed (citten, not_lit);
  int res = sweep_solve ();
  if (res == 10) {
    LOG ("sweeping backbone candidate %d failed", lit);
    sweep_refine (sweeper);
    stats.sweep_sat_backbone++;
    return false;
  }

  if (res == 20) {
    LOG ("sweep unit %d", lit);
    save_add_clear_core (sweeper);
    stats.sweep_unsat_backbone++;
    return true;
  }

  stats.sweep_unknown_backbone++;

  LOG ("sweeping backbone candidate %d failed", lit);
  return false;
}

void Internal::add_sweep_binary (int lit, int other) {
  // kissat_new_binary_clause (solver, lit, other);
  // TODO potentially only add for proof -> similar to decompose...
  /*
    LOG ("marking equivalence of %d and %d", idx, other);
    assert (clause.empty ());
    assert (lrat_chain.empty ());
    clause.push_back (other);
    clause.push_back (-idx);
    if (lrat) {
      build_lrat_for_clause (dfs_chains);
      assert (!lrat_chain.empty ());
    }

    const uint64_t id1 = ++clause_id;
    if (proof) {
      proof->add_derived_clause (id1, false, clause, lrat_chain);
      proof->weaken_minus (id1, clause);
    }
    external->push_binary_clause_on_extension_stack (id1, -idx, other);

    decompose_ids[vlit (-idx)] = id1;

    lrat_chain.clear ();
    clause.clear ();

    assert (clause.empty ());
    assert (lrat_chain.empty ());
    clause.push_back (idx);
    clause.push_back (-other);
    if (lrat) {
      build_lrat_for_clause (dfs_chains);
      assert (!lrat_chain.empty ());
    }
    const uint64_t id2 = ++clause_id;
    if (proof) {
      proof->add_derived_clause (id2, false, clause, lrat_chain);
      proof->weaken_minus (id2, clause);
    }
    external->push_binary_clause_on_extension_stack (id2, idx, -other);
    decompose_ids[vlit (idx)] = id2;

    clause.clear ();
    lrat_chain.clear ();
*/
  return;
}

bool Internal::scheduled_variable (Sweeper &sweeper, int idx) {
  return sweeper.prev[idx] != 0 || sweeper.first == idx;
}

void Internal::schedule_inner (Sweeper &sweeper, int idx) {
  assert (idx);
  if (!active (idx))
    return;
  const int next = sweeper.next[idx];
  if (next != 0) {
    LOG ("rescheduling inner %d as last", idx);
    const unsigned prev = sweeper.prev[idx];
    assert (sweeper.prev[next] == idx);
    sweeper.prev[next] = prev;
    if (prev == 0) {
      assert (sweeper.first == idx);
      sweeper.first = next;
    } else {
      assert (sweeper.next[prev] == idx);
      sweeper.next[prev] = next;
    }
    const unsigned last = sweeper.last;
    if (last == 0) {
      assert (sweeper.first == 0);
      sweeper.first = idx;
    } else {
      assert (sweeper.next[last] == 0);
      sweeper.next[last] = idx;
    }
    sweeper.prev[idx] = last;
    sweeper.next[idx] = 0;
    sweeper.last = idx;
  } else if (sweeper.last != idx) {
    LOG ("scheduling inner %d as last", idx);
    const unsigned last = sweeper.last;
    if (last == 0) {
      assert (sweeper.first == 0);
      sweeper.first = idx;
    } else {
      assert (sweeper.next[last] == 0);
      sweeper.next[last] = idx;
    }
    assert (sweeper.next[idx] == 0);
    sweeper.prev[idx] = last;
    sweeper.last = idx;
  } else
    LOG ("keeping inner %d scheduled as last", idx);
}

void Internal::schedule_outer (Sweeper &sweeper, int idx) {
  assert (!scheduled_variable (sweeper, idx));
  assert (active (idx));
  const int first = sweeper.first;
  if (first == 0) {
    assert (sweeper.last == 0);
    sweeper.last = idx;
  } else {
    assert (sweeper.prev[first] == 0);
    sweeper.prev[first] = idx;
  }
  assert (sweeper.prev[idx] == 0);
  sweeper.next[idx] = first;
  sweeper.first = idx;
  LOG ("scheduling outer %d as first", idx);
}

int Internal::next_scheduled (Sweeper &sweeper) {
  int res = sweeper.last;
  if (res == 0) {
    LOG ("no more scheduled variables left");
    return 0;
  }
  assert (res > 0);
  LOG ("dequeuing next scheduled %d", res);
  const unsigned prev = sweeper.prev[res];
  assert (sweeper.next[res] == 0);
  sweeper.prev[res] = 0;
  if (prev == 0) {
    assert (sweeper.first == res);
    sweeper.first = 0;
  } else {
    assert (sweeper.next[prev] == res);
    sweeper.next[prev] = 0;
  }
  sweeper.last = prev;
  return res;
}

#define all_scheduled(IDX) \
  int IDX = sweeper.first, NEXT_##IDX; \
  IDX != 0 && (NEXT_##IDX = sweeper.next[IDX], true); \
  IDX = NEXT_##IDX

  
void Internal::substitute_connected_clauses (Sweeper &sweeper, int lit,
                                          int repr) {
  if (unsat)
    return;
  if (val (lit))
    return;
  if (val (repr))
    return;
  LOG ("substituting %d with %d in all irredundant clauses", lit, repr);

  assert (lit != repr);
  assert (lit != -repr);

  assert (active (lit));
  assert (active (repr));


  {
    Occs &ns = occs (lit);
    auto const begin = ns.begin ();
    const auto end = ns.end ();
    auto q = begin;
    auto p = q;
    while (p != end) {
      Clause *c = *q++ = *p++;
      if (c->garbage)
        continue;
      assert (clause.empty ());
      bool satisfied = false;
      bool repr_already_watched = false;
      const int not_repr = -repr;
#ifndef NDEBUG
      bool found = false;
#endif
      for (const auto & other : *c) {
        if (other == lit) {
#ifndef NDEBUG
          assert (!found);
          found = true;
#endif
          clause.push_back (repr);
          continue;
        }
        assert (other != -lit);
        if (other == repr) {
          assert (!repr_already_watched);
          repr_already_watched = true;
          continue;
        }
        if (other == not_repr) {
          satisfied = true;
          break;
        }
        const signed char tmp = val (other);
        if (tmp < 0)
          continue;
        if (tmp > 0) {
          satisfied = true;
          break;
        }
        clause.push_back (other);
      }
      if (satisfied) {
        clause.clear ();
        mark_garbage (c);
        continue;
      }
      assert (found);
      const unsigned new_size = clause.size ();
      if (new_size == 0) {
        LOG (c, "substituted empty clause");
        assert (!unsat);
        learn_empty_clause ();
        break;
      }
      if (new_size == 1) {
        LOG (c, "reduces to unit");
        const int unit = clause[0];
        clause.clear ();
        assign_unit (unit);
        sweeper.propagate.push_back (unit);
        mark_garbage (c);
        stats.sweep_units++;
        break;
      }
      assert (c->size >= 2);
      if (!c->redundant)
        mark_removed (c);
      if (proof) {
        proof->add_derived_clause (++clause_id, c->redundant, clause,
                                   lrat_chain);
        proof->delete_clause (c);
        c->id = clause_id;
      }
      size_t l;
      int *literals = c->literals;
      for (l = 0; l < clause.size (); l++)
        literals[l] = clause[l];
      int flushed = c->size - (int) l;
      if (flushed) {
        LOG ("flushed %d literals", flushed);
        (void) shrink_clause (c, l);
      } else if (likely_to_be_kept_clause (c))
        mark_added (c);
      LOG (c, "substituted");
      if (!repr_already_watched)     // TODO maybe delay this
        occs (repr).push_back (c);
      clause.clear ();
      q--;
    }
    while (p != end)
      *q++ = *p++;
    ns.resize (q - ns.begin ());
  }
}

void Internal::sweep_remove (Sweeper &sweeper, int lit) {
  assert (sweeper.reprs[lit] != lit);
  vector<int> &partition = sweeper.partition;
  const auto begin_partition = partition.begin ();
  auto p = begin_partition;
  const auto end_partition = partition.end ();
  for (; *p != lit; p++)
    assert (p + 1 != end_partition);
  auto begin_class = p;
  while (begin_class != begin_partition && begin_class[-1] != 0)
    begin_class--;
  auto end_class = p;
  while (*end_class != 0)
    end_class++;
  const unsigned size = end_class - begin_class;
  LOG ("removing non-representative %d from equivalence class of size %u",
       lit, size);
  assert (size > 1);
  auto q = begin_class;
  if (size == 2) {
    LOG ("completely squashing equivalence class of %d", lit);
    for (auto r = end_class + 1; r != end_partition; r++)
      *q++ = *r;
  } else {
    for (auto r = begin_class; r != end_partition; r++)
      if (r != p)
        *q++ = *r;
  }
  partition.resize (q - partition.begin ());
}

void Internal::flip_partition_literals (Sweeper &sweeper) {
  const unsigned max_rounds = opts.sweepfliprounds;
  if (!max_rounds)
    return;
  assert (sweeper.partition.size ());
  if (kitten_status (citten) != 10)
    return;
#ifdef LOGGING
  unsigned total_flipped = 0;
#endif
  unsigned flipped, round = 0;
  do {
    round++;
    flipped = 0;
    auto begin = sweeper.partition.begin (), dst = begin, src = dst;
    const auto end = sweeper.partition.end ();
    while (src != end) {
      auto end_src = src;
      while (assert (end_src != end), *end_src != 0)
        end_src++;
      unsigned size = end_src - src;
      assert (size > 1);
      auto q = dst;
      for (auto p = src; p != end_src; p++) {
        const int lit = *p;
        if (kitten_flip_signed_literal (citten, lit)) {
          LOG ("flipping equivalence candidate %d succeeded", lit);
#ifdef LOGGING
          total_flipped++;
#endif
          flipped++;
          if (--size < 2)
            break;
        } else {
          LOG ("flipping equivalence candidate %d failed", lit);
          *q++ = lit;
        }
      }
      if (size > 1) {
        *q++ = 0;
        dst = q;
      }
      src = end_src + 1;
    }
    sweeper.partition.resize (dst - sweeper.partition.begin ());
    LOG ("flipped %u equivalence candidates in round %u", flipped, round);

    if (terminated_asynchronously ())
      break;
    if (kitten_current_ticks (citten) > sweeper.limit.ticks)
      break;
  } while (flipped && round < max_rounds);
  LOG ("flipped %u equivalence candidates in total in %u rounds",
       total_flipped, round);
}

bool Internal::sweep_equivalence_candidates (Sweeper &sweeper, int lit,
                                          int other) {
  LOG ("trying equivalence candidates %d = %d", lit,
       other);
  const int not_other = -other;
  const int not_lit = -lit;
  const auto begin = sweeper.partition.begin ();
  auto const end = sweeper.partition.end ();
  assert (begin + 3 <= end);
  assert (end[-3] == lit);
  assert (end[-2] == other);
  const int third = (end - begin == 3) ? 0 : end[-4];
  const int status = kitten_status (citten);
  if (status == 10 && kitten_flip_signed_literal (citten, lit)) {
    stats.sweep_flip_equivalences++;
    stats.sweep_flipped_equivalences++;
    LOG ("flipping %d succeeded", lit);
    if (third == 0) {
      LOG ("squashing equivalence class of %d", lit);
      sweeper.partition.resize (sweeper.partition.size () - 3);
    } else {
      LOG ("removing %d from equivalence class of %d", lit,
           other);
      end[-3] = other;
      end[-2] = 0;
      sweeper.partition.resize (sweeper.partition.size () - 1);
    }
    // LOGPARTITION ("refined equivalence candidates");
    return false;
  } else if (status == 10 && kitten_flip_signed_literal (citten, other)) {
    stats.sweep_flip_equivalences += 2;
    stats.sweep_flipped_equivalences++;
    LOG ("flipping %d succeeded", other);
    if (third == 0) {
      LOG ("squashing equivalence class of %d", lit);
      sweeper.partition.resize (sweeper.partition.size () - 3);
    } else {
      LOG ("removing %d from equivalence class of %d", other,
           lit);
      end[-2] = 0;
      sweeper.partition.resize (sweeper.partition.size () - 1);
    }
    // LOGPARTITION ("refined equivalence candidates");
    return false;
  }
  if (status == 10)
    stats.sweep_flip_equivalences += 2;
  LOG ("flipping %d and %d both failed", lit, other);
  kitten_assume_signed (citten, not_lit);
  kitten_assume_signed (citten, other);
  stats.sweep_solved_equivalences++;
  int res = sweep_solve ();
  if (res == 10) {
    stats.sweep_sat_equivalences++;
    LOG ("first sweeping implication %d -> %d failed", other,
         lit);
    sweep_refine (sweeper);
  } else if (!res) {
    stats.sweep_unknown_equivalences++;
    LOG ("first sweeping implication %d -> %d hit ticks limit",
         other, lit);
  }

  if (res != 20)
    return false;

  stats.sweep_unsat_equivalences++;
  LOG ("first sweeping implication %d -> %d succeeded", other,
       lit);

  save_core (sweeper, 0);

  kitten_assume_signed (citten, lit);
  kitten_assume_signed (citten, not_other);
  res = sweep_solve ();
  stats.sweep_solved_equivalences++;
  if (res == 10) {
    stats.sweep_sat_equivalences++;
    LOG ("second sweeping implication %d <- %d failed", other,
         lit);
    sweep_refine (sweeper);
  } else if (!res) {
    stats.sweep_unknown_equivalences++;
    LOG ("second sweeping implication %d <- %d hit ticks limit",
         other, lit);
  }

  if (res != 20) {
    sweeper.core[0].clear ();
    return false;
  }

  stats.sweep_unsat_equivalences++;
  LOG ("second sweeping implication %d <- %d succeeded too", other,
       lit);

  save_core (sweeper, 1);

  LOG ("sweep equivalence %d = %d", lit, other);
  stats.sweep_equivalences++;

  add_core (sweeper, 0);
  add_sweep_binary (lit, not_other);
  clear_core (sweeper, 0);

  add_core (sweeper, 1);
  add_sweep_binary (not_lit, other);
  clear_core (sweeper, 1);

  int repr;
  if (lit < other) {
    repr = sweeper.reprs[other] = lit;
    sweeper.reprs[not_other] = not_lit;
    substitute_connected_clauses (sweeper, other, lit);
    substitute_connected_clauses (sweeper, not_other, not_lit);
    sweep_remove (sweeper, other);
  } else {
    repr = sweeper.reprs[lit] = other;
    sweeper.reprs[not_lit] = not_other;
    substitute_connected_clauses (sweeper, lit, other);
    substitute_connected_clauses (sweeper, not_lit, not_other);
    sweep_remove (sweeper, lit);
  }

  const int repr_idx = abs (repr);
  schedule_inner (sweeper, repr_idx);

  return true;
}

const char *Internal::sweep_variable (Sweeper &sweeper, int idx) {
  assert (!unsat);
  if (!active (idx))
    return "inactive variable";
  const int start = idx;
  if (sweeper.reprs[start] != start)
    return "non-representative variable";
  assert (sweeper.vars.empty ());
  assert (sweeper.refs.empty ());
  assert (sweeper.backbone.empty ());
  assert (sweeper.partition.empty ());
  assert (!sweeper.encoded);

  stats.sweep_variables++;

  LOG ("sweeping %d", idx);
  assert (!val (start));
  LOG ("starting sweeping[0]");
  add_literal_to_environment (sweeper, 0, start);
  LOG ("finished sweeping[0]");
  LOG ("starting sweeping[1]");

  bool limit_reached = false;
  size_t expand = 0, next = 1;
  bool success = false;
  unsigned depth = 1;

  while (!limit_reached) {
    if (sweeper.encoded >= sweeper.limit.clauses) {
      LOG ("environment clause limit reached");
      limit_reached = true;
      break;
    }
    if (expand == next) {
      LOG ("finished sweeping[%u]", depth);
      if (depth >= sweeper.limit.depth) {
        LOG ("environment depth limit reached");
        break;
      }
      next = sweeper.vars.size ();
      if (expand == next) {
        LOG ("completely copied all clauses");
        break;
      }
      depth++;
      LOG ("starting sweeping[%u]", depth);
    }
    const unsigned choices = next - expand;
    if (opts.sweeprand && choices > 1) {
      const unsigned swaps =
          sweeper.random.pick_int (0, choices);
      if (swaps) {
        swap (sweeper.vars[expand], sweeper.vars[expand + swaps]);
      }
    }
    const int idx = sweeper.vars[expand];
    LOG ("traversing and adding clauses of %d", idx);
    for (unsigned sign = 0; sign < 2; sign++) {
      const int lit = sign ? -idx : idx;
      Occs &ns = occs (lit);
      for (auto c : ns) {
        sweep_clause (sweeper, depth, c);
        if (sweeper.vars.size () >= sweeper.limit.vars) {
          LOG ("environment variable limit reached");
          limit_reached = true;
          break;
        }
      }
      if (limit_reached)
        break;
    }
    expand++;
  }
  stats.sweep_depth += depth;
  stats.sweep_clauses += sweeper.encoded;
  stats.sweep_environment += sweeper.vars.size ();
  VERBOSE (3,
                            "sweeping variable %d environment of "
                            "%zu variables %u clauses depth %u",
                            externalize (idx),
                            sweeper.vars.size (), sweeper.encoded,
                            depth);
  int res = sweep_solve ();
  LOG ("sub-solver returns '%d'", res);
  if (res == 10) {
    init_backbone_and_partition (sweeper);
#ifndef QUIET
    uint64_t units = stats.sweep_units;
    uint64_t solved = stats.sweep_solved;
#endif
    START (sweepbackbone);
    while (sweeper.backbone.size ()) {
      if (unsat || terminated_asynchronously () ||
          kitten_ticks_limit_hit (sweeper, "backbone refinement")) {
        limit_reached = true;
      STOP_SWEEP_BACKBONE:
        STOP (sweepbackbone);
        goto DONE;
      }
      flip_backbone_literals (sweeper);
      if (terminated_asynchronously () ||
          kitten_ticks_limit_hit (sweeper, "backbone refinement")) {
        limit_reached = true;
        goto STOP_SWEEP_BACKBONE;
      }
      if (sweeper.backbone.empty ())
        break;
      const int lit = sweeper.backbone.back ();
      sweeper.backbone.pop_back ();
      if (!active (lit))
        continue;
      if (sweep_backbone_candidate (sweeper, lit))
        success = true;
    }
    STOP (sweepbackbone);
#ifndef QUIET
    units = stats.sweep_units - units;
    solved = stats.sweep_solved - solved;
#endif
    VERBOSE (3,
        "complete swept variable %d backbone with %" PRIu64
        " units in %" PRIu64 " solver calls",
        externalize (idx), units, solved);
    assert (EMPTY_STACK (sweeper.backbone));
#ifndef QUIET
    uint64_t equivalences = stats.sweep_equivalences;
    solved = stats.sweep_solved;
#endif
    START (sweepequivalences);
    while (sweeper.partition.size ()) {
      if (unsat || terminated_asynchronously () ||
          kitten_ticks_limit_hit (sweeper, "partition refinement")) {
        limit_reached = true;
      STOP_SWEEP_EQUIVALENCES:
        STOP (sweepequivalences);
        goto DONE;
      }
      flip_partition_literals (sweeper);
      if (terminated_asynchronously () ||
          kitten_ticks_limit_hit (sweeper, "backbone refinement")) {
        limit_reached = true;
        goto STOP_SWEEP_EQUIVALENCES;
      }
      if (sweeper.partition.empty ())
        break;
      if (sweeper.partition.size () > 2) {
        const auto end = sweeper.partition.end ();
        assert (end[-1] == 0);
        int lit = end[-3];
        int other = end[-2];
        if (sweep_equivalence_candidates (sweeper, lit, other))
          success = true;
      } else
        sweeper.partition.clear ();
    }
    STOP (sweepequivalences);
#ifndef QUIET
    equivalences = stats.sweep_equivalences - equivalences;
    solved = stats.sweep_solved - solved;
    if (equivalences)
      VERBOSE (3,
          "complete swept variable %d partition with %" PRIu64
          " equivalences in %" PRIu64 " solver calls",
          externalize (idx), equivalences, solved);
#endif
  } else if (res == 20)
    sweep_empty_clause (sweeper);

DONE:
  clear_sweeper (sweeper);

  if (!unsat)
    sweep_dense_propagate (sweeper);

  if (success && limit_reached)
    return "successfully despite reaching limit";
  if (!success && !limit_reached)
    return "unsuccessfully without reaching limit";
  else if (success && !limit_reached)
    return "successfully without reaching limit";
  assert (!success && limit_reached);
  return "unsuccessfully and reached limit";
}

struct sweep_candidate {
  unsigned rank;
  int idx;
};

struct rank_sweep_candidate {
  bool operator() (sweep_candidate a, sweep_candidate b) const {
    assert (a.rank && b.rank);
    assert (a.idx > 0 && b.idx > 0);
    if (a.rank < b.rank) return true;
    if (b.rank < a.rank) return false;
    return a.idx < b.idx;
  }
};

bool Internal::scheduable_variable (Sweeper &sweeper, int idx,
                                    size_t *occ_ptr) {
  const int lit = idx;
  const size_t pos = watches (lit).size ();
  if (!pos)
    return false;
  const unsigned max_occurrences = sweeper.limit.clauses;
  if (pos > max_occurrences)
    return false;
  const int not_lit = -lit;
  const size_t neg = watches (not_lit).size ();
  if (!neg)
    return false;
  if (neg > max_occurrences)
    return false;
  *occ_ptr = pos + neg;
  return true;
}

unsigned Internal::schedule_all_other_not_scheduled_yet (Sweeper &sweeper) {
  vector<sweep_candidate> fresh;
  for (const auto & idx : vars) {
    Flags &f = flags (idx);
    if (!f.active ())
      continue;
    if (sweep_incomplete && !f.sweep)
      continue;
    if (scheduled_variable (sweeper, idx))
      continue;
    size_t occ;
    if (!scheduable_variable (sweeper, idx, &occ)) {
      f.sweep = false;
      continue;
    }
    sweep_candidate cand;
    cand.rank = occ;
    cand.idx = idx;
    fresh.push_back (cand);
  }
  const size_t size = fresh.size ();
  assert (size <= UINT_MAX);
  sort (fresh.begin (), fresh.end (), rank_sweep_candidate ());
  for (auto &cand : fresh)
    schedule_outer (sweeper, cand.idx);
  return size;
}

unsigned Internal::reschedule_previously_remaining (Sweeper &sweeper) {
  unsigned rescheduled = 0;
  for (const auto & idx : sweep_schedule) {
    Flags &f = flags (idx);
    if (!f.active ())
      continue;
    if (scheduled_variable (sweeper, idx))
      continue;
    size_t occ;
    if (!scheduable_variable (sweeper, idx, &occ)) {
      f.sweep = false;
      continue;
    }
    schedule_inner (sweeper, idx);
    rescheduled++;
  }
  sweep_schedule.clear ();
  return rescheduled;
}

unsigned Internal::incomplete_variables (Sweeper &sweeper) {
  unsigned res = 0;
  for (const auto &idx : vars) {
    Flags &f = flags (idx);
    if (!f.active ())
      continue;
    if (f.sweep)
      res++;
  }
  return res;
}

void Internal::mark_incomplete (Sweeper &sweeper) {
  unsigned marked = 0;
  for (all_scheduled (idx))
    if (!flags (idx).sweep) {
      flags (idx).sweep = true;
      marked++;
    }
  sweep_incomplete = true;
#ifndef QUIET
  VERBOSE (2,
      "marked %u scheduled sweeping variables as incomplete",
      marked);
#else
  (void) marked;
#endif
}

unsigned Internal::schedule_sweeping (Sweeper &sweeper) {
  const unsigned rescheduled = reschedule_previously_remaining (sweeper);
  const unsigned fresh = schedule_all_other_not_scheduled_yet (sweeper);
  const unsigned scheduled = fresh + rescheduled;
  const unsigned incomplete = incomplete_variables (sweeper);
#ifndef QUIET
  PHASE ("sweep", stats.sweep,
                "scheduled %u variables %.0f%% "
                "(%u rescheduled %.0f%%, %u incomplete %.0f%%)",
                scheduled, percent (scheduled, active ()),
                rescheduled, percent (rescheduled, scheduled),
                incomplete, percent (incomplete, scheduled));
#endif
  if (incomplete)
    assert (sweep_incomplete);
  else {
    if (sweep_incomplete)
      stats.sweep_completed++;
    mark_incomplete (sweeper);
  }
  return scheduled;
}

void Internal::unschedule_sweeping (Sweeper &sweeper, unsigned swept,
                                 unsigned scheduled) {
#ifdef QUIET
  (void) scheduled, (void) swept;
#endif
  assert (sweep_schedule.empty ());
  assert (sweep_incomplete);
  for (all_scheduled (idx))
    if (active (idx)) {
      sweep_schedule.push_back (idx);
      LOG ("untried scheduled %d", idx);
    }
#ifndef QUIET
  const unsigned retained = sweep_schedule.size ();
#endif
  VERBOSE (3, "retained %u variables %.0f%% to be swept next time",
      retained, percent (retained, active ()));
  const unsigned incomplete = incomplete_variables (sweeper);
  if (incomplete)
    VERBOSE (3, "need to sweep %u more variables %.0f%% for completion",
            incomplete, percent (incomplete, active ()));
  else {
    VERBOSE (3, "no more variables needed to complete sweep");
    sweep_incomplete = false;
    stats.sweep_completed++;
  }
  PHASE ("sweep", stats.sweep,
                "swept %u variables (%u remain %.0f%%)", swept, incomplete,
                percent (incomplete, scheduled));
}

bool Internal::sweep () {
  if (opts.sweep)
    return false;
  if (unsat)
    return false;
  if (terminated_asynchronously ())
    return false;
//  if (DELAYING (sweep))  TODO sweeping should not be called every probe but
//    return false;             only sometimes based on a counter
  assert (!level);
  // assert (!solver->unflushed);  // ? maybe flushed falsified literals from clauses??
  START (sweep);
  stats.sweep++;
  uint64_t equivalences = stats.sweep_equivalences;
  uint64_t units = stats.sweep_units;
  Sweeper sweeper = Sweeper (this);
  const unsigned scheduled = schedule_sweeping (sweeper);
  uint64_t swept = 0, limit = 10;
  for (;;) {
    if (unsat)
      break;
    if (terminated_asynchronously ())
      break;
    if (kitten_current_ticks (citten) > sweeper.limit.ticks)
      break;
    int idx = next_scheduled (sweeper);
    if (idx == 0)
      break;
    flags (idx).sweep = false;
#ifndef QUIET
    const char *res =
#endif
        sweep_variable (sweeper, idx);
    VERBOSE (2, "swept[%" PRIu64 "] external variable %d %s", swept,
        externalize (idx), res);
    if (++swept == limit) {
      VERBOSE (2,
                           "found %" PRIu64 " equivalences and %" PRIu64
                           " units after sweeping %" PRIu64 " variables ",
                           stats.sweep_equivalences - equivalences,
                           stats.sweep_units - units, swept);
      limit *= 10;
    }
  }
  VERBOSE (2, "swept %" PRIu64 " variables", swept);
  equivalences = stats.sweep_equivalences - equivalences,
  units = stats.sweep_units - units;
  PHASE ("sweep", stats.sweep,
                "found %" PRIu64 " equivalences and %" PRIu64 " units",
                equivalences, units);
  unschedule_sweeping (sweeper, swept, scheduled);
  unsigned inactive = release_sweeper (sweeper);

  if (!unsat) {
    propagated = 0;
    if (!propagate ()) {
      learn_empty_clause ();
    }
  }

  uint64_t eliminated = equivalences + units;
#ifndef QUIET
  // assert (active () >= inactive);
  // solver->active -= inactive;   // don't know if this is allowed !!
  report ('=', !eliminated);
  // solver->active += inactive;
#else
  (void) inactive;
#endif
//  if (kissat_average (eliminated, swept) < 0.001)
//    BUMP_DELAY (sweep);              // increase sweeping counter (see above)
//  else
//    REDUCE_DELAY (sweep);            // decrease sweeping counter
  STOP (sweep);
  return eliminated;
}

}