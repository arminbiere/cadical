#include "internal.hpp"

struct Sweeper {
  Sweeper Sweeper (Internal *internal);
  Sweeper ~Sweeper ();
  Internal *internal;
  vector<unsigned> depths;
  int* reprs;
  vector<int> next, prev;
  int first, last;
  unsigned encoded;
  unsigned save;
  vector<int> vars;
  vector<Clause *> clauses;
  vector<unsigned> clause;
  vector<unsigned> backbone;
  vector<unsigned> partition;
  vector<unsigned> core[2];
  struct {
    uint64_t ticks;
    unsigned clauses, depth, vars;
  } limit;
};

void Sweeper::Sweeper (Internal *i) : internal (i) {
  internal->init_sweeper (this);
}
void Sweeper::~Sweeper () {
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
  enlarge_zero (sweeper.depths, max_var + 1)
  sweeper.reprs = new int[2 * max_var + 1];
  sweeper.reprs -= max_var;
  enlarge_zero (sweeper.prev, max_var + 1)
  enlarge_zero (sweeper.next, max_var + 1)
  for (const auto & lit : lits)
    sweeper.reprs[lit] = lit;
  sweeper.first = sweeper.last = 0;
  assert (!citten);
  citten = kitten_init ();
  kitten_track_antecedents (citten);

  kissat_enter_dense_mode (solver, 0); // TODO: full occurence list
  kissat_connect_irredundant_large_clauses (solver);

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
  VERBOSE (solver, "sweeper variable limit %u",
                            sweeper.limit.vars);

  uint64_t depth_limit = solver.statistics.sweep_completed;
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
  
  kitten_release (citten);
  citten = 0;
  kissat_resume_sparse_mode (solver, false, 0);
  return merged;
}

void Internal::clear_sweeper (Sweeper &sweeper) {
  LOG ("clearing sweeping environment");
  kitten_clear (citten);
  kitten_track_antecedents (citten);
  for (auto & idx : sweeper.vars)) {
    assert (sweeper.depths[idx]);
    sweeper.depths[idx] = 0;
  }
  sweeper.vars.clear ():
  for (auto c : sweeper.clauses)) {
    assert (c->swept);
    c->swept = false;
  }
  sweeper.clauses.clear ();
  sweeper.backbone.clear ();
  sweeper.partition.clear ();
  sweeper.encoded = 0;
  sweep_set_kitten_ticks_limit (sweeper);
}

unsigned Internal::sweep_repr (Sweeper &sweeper, unsigned lit) {
  unsigned res;
  {
    unsigned prev = lit;
    while ((res = sweeper->reprs[prev]) != prev)
      prev = res;
  }
  if (res == lit)
    return res;
#if defined(LOGGING) || !defined(NDEBUG)
  kissat *solver = sweeper->solver;
#endif
  LOG ("sweeping repr[%s] = %s", LOGLIT (lit), LOGLIT (res));
  {
    const unsigned not_res = NOT (res);
    unsigned next, prev = lit;
    ;
    while ((next = sweeper->reprs[prev]) != res) {
      const unsigned not_prev = NOT (prev);
      sweeper->reprs[not_prev] = not_res;
      sweeper->reprs[prev] = res;
      prev = next;
    }
    assert (sweeper->reprs[NOT (prev)] == not_res);
  }
  return res;
}

void Internal::add_literal_to_environment (Sweeper &sweeper, unsigned depth,
                                        unsigned lit) {
  const unsigned repr = sweep_repr (sweeper, lit);
  if (repr != lit)
    return;
  const unsigned idx = IDX (lit);
  if (sweeper->depths[idx])
    return;
  assert (depth < UINT_MAX);
  sweeper->depths[idx] = depth + 1;
  PUSH_STACK (sweeper->vars, idx);
  LOG ("sweeping[%u] adding literal %s", depth, LOGLIT (lit));
}

void Internal::sweep_clause (Sweeper &sweeper, unsigned depth) {
  kissat *solver = sweeper->solver;
  assert (SIZE_STACK (sweeper->clause) > 1);
  for (all_stack (unsigned, lit, sweeper->clause))
    add_literal_to_environment (sweeper, depth, lit);
  kitten_clause (solver->kitten, SIZE_STACK (sweeper->clause),
                 BEGIN_STACK (sweeper->clause));
  CLEAR_STACK (sweeper->clause);
  sweeper->encoded++;
}

void sweep_binary Internal::(Sweeper &sweeper, unsigned depth, unsigned lit,
                          unsigned other) {
  if (sweep_repr (sweeper, lit) != lit)
    return;
  if (sweep_repr (sweeper, other) != other)
    return;
  kissat *solver = sweeper->solver;
  LOGBINARY (lit, other, "sweeping[%u]", depth);
  value *values = solver->values;
  assert (!values[lit]);
  const value other_value = values[other];
  if (other_value > 0) {
    LOGBINARY (lit, other, "skipping satisfied");
    return;
  }
  const unsigned *depths = sweeper->depths;
  const unsigned other_idx = IDX (other);
  const unsigned other_depth = depths[other_idx];
  const unsigned lit_idx = IDX (lit);
  const unsigned lit_depth = depths[lit_idx];
  if (other_depth && other_depth < lit_depth) {
    LOGBINARY (lit, other, "skipping depth %u copied", other_depth);
    return;
  }
  assert (!other_value);
  assert (EMPTY_STACK (sweeper->clause));
  PUSH_STACK (sweeper->clause, lit);
  PUSH_STACK (sweeper->clause, other);
  sweep_clause (sweeper, depth);
}

void Internal::sweep_reference (Sweeper &sweeper, unsigned depth,
                             reference ref) {
  assert (EMPTY_STACK (sweeper->clause));
  kissat *solver = sweeper->solver;
  clause *c = kissat_dereference_clause (solver, ref);
  if (c->swept)
    return;
  if (c->garbage)
    return;
  LOGCLS (c, "sweeping[%u]", depth);
  value *values = solver->values;
  for (all_literals_in_clause (lit, c)) {
    const value value = values[lit];
    if (value > 0) {
      kissat_mark_clause_as_garbage (solver, c);
      CLEAR_STACK (sweeper->clause);
      return;
    }
    if (value < 0)
      continue;
    PUSH_STACK (sweeper->clause, lit);
  }
  PUSH_STACK (sweeper->refs, ref);
  c->swept = true;
  sweep_clause (sweeper, depth);
}

extern 'C' {
static void save_core_clause (void *state, bool learned, size_t size,
                              const unsigned *lits) {
  Sweeper &sweeper = state;
  Internal *internal = sweeper.internal;
  if (internal->inconsistent)
    return;
  const value *const values = solver->values;
  unsigneds *core = sweeper->core + sweeper->save;
  size_t saved = SIZE_STACK (*core);
  const unsigned *end = lits + size;
  unsigned non_false = 0;
  for (const unsigned *p = lits; p != end; p++) {
    const unsigned lit = *p;
    const value value = values[lit];
    if (value > 0) {
      LOGLITS (size, lits, "extracted %s satisfied lemma", LOGLIT (lit));
      RESIZE_STACK (*core, saved);
      return;
    }
    PUSH_STACK (*core, lit);
    if (value < 0)
      continue;
    if (!learned && ++non_false > 1) {
      LOGLITS (size, lits, "ignoring extracted original clause");
      RESIZE_STACK (*core, saved);
      return;
    }
  }
#ifdef LOGGING
  unsigned *saved_lits = BEGIN_STACK (*core) + saved;
  size_t saved_size = SIZE_STACK (*core) - saved;
  LOGLITS (saved_size, saved_lits, "saved core[%u]", sweeper->save);
#endif
  PUSH_STACK (*core, INVALID_LIT);
}
} // end extern C

void Internal::add_core (Sweeper &sweeper, unsigned core_idx) {
  if (unsat)
    return;
  LOG ("check and add extracted core[%u] lemmas to proof", core_idx);
  assert (core_idx == 0 || core_idx == 1);
  unsigneds *core = sweeper->core + core_idx;
  const value *const values = solver->values;

  unsigned *q = BEGIN_STACK (*core);
  const unsigned *const end_core = END_STACK (*core), *p = q;

  while (p != end_core) {
    const unsigned *c = p;
    while (*p != INVALID_LIT)
      p++;
#ifdef LOGGING
    size_t old_size = p - c;
    LOGLITS (old_size, c, "simplifying extracted core[%u] lemma", core_idx);
#endif
    bool satisfied = false;
    unsigned unit = INVALID_LIT;

    unsigned *d = q;

    for (const unsigned *l = c; !satisfied && l != p; l++) {
      const unsigned lit = *l;
      const value value = values[lit];
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
      CHECK_AND_ADD_EMPTY ();
      ADD_EMPTY_TO_PROOF ();
      solver->inconsistent = true;
      CLEAR_STACK (*core);
      return;
    }

    if (new_size == 1) {
      q = d;
      assert (unit != INVALID_LIT);
      LOG ("sweeping produced unit %s", LOGLIT (unit));
      CHECK_AND_ADD_UNIT (unit);
      ADD_UNIT_TO_PROOF (unit);
      kissat_assign_unit (solver, unit, "sweeping backbone reason");
      stats.sweep_units++;
      continue;
    }

    *q++ = INVALID_LIT;

    assert (new_size > 1);
    LOGLITS (new_size, d, "adding extracted core[%u] lemma", core_idx);
    CHECK_AND_ADD_LITS (new_size, d);
    ADD_LITS_TO_PROOF (new_size, d);
  }
  SET_END_OF_STACK (*core, q);
#ifndef LOGGING
  (void) core_idx;
#endif
}

void Internal::save_core (Sweeper &sweeper, unsigned core) {
  kissat *solver = sweeper->solver;
  LOG ("saving extracted core[%u] lemmas", core);
  assert (core == 0 || core == 1);
  assert (EMPTY_STACK (sweeper->core[core]));
  sweeper->save = core;
  kitten_compute_clausal_core (solver->kitten, 0);
  kitten_traverse_core_clauses (solver->kitten, sweeper, save_core_clause);
}

void Internal::clear_core (Sweeper &sweeper, unsigned core_idx) {
  if (unsat)
    return;
#if defined(LOGGING) || !defined(NDEBUG) || !defined(NPROOFS)
  assert (core_idx == 0 || core_idx == 1);
  LOG ("clearing core[%u] lemmas", core_idx);
#endif
  unsigneds *core = sweeper->core + core_idx;
#ifdef CHECKING_OR_PROVING
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
#endif
  CLEAR_STACK (*core);
}

void Internal::save_add_clear_core (Sweeper &sweeper) {
  save_core (sweeper, 0);
  add_core (sweeper, 0);
  clear_core (sweeper, 0);
}

#define LOGBACKBONE(MESSAGE) \
  LOGLITSET (SIZE_STACK (sweeper->backbone), \
             BEGIN_STACK (sweeper->backbone), MESSAGE)

#define LOGPARTITION(MESSAGE) \
  LOGLITPART (SIZE_STACK (sweeper->partition), \
              BEGIN_STACK (sweeper->partition), MESSAGE)

void Internal::init_backbone_and_partition (Sweeper &sweeper) {
  kissat *solver = sweeper->solver;
  LOG ("initializing backbone and equivalent literals candidates");
  for (all_stack (unsigned, idx, sweeper->vars)) {
    if (!ACTIVE (idx))
      continue;
    const unsigned lit = LIT (idx);
    const unsigned not_lit = NOT (lit);
    const signed char tmp = kitten_value (citten, lit);
    const unsigned candidate = (tmp < 0) ? not_lit : lit;
    LOG ("sweeping candidate %s", LOGLIT (candidate));
    PUSH_STACK (sweeper->backbone, candidate);
    PUSH_STACK (sweeper->partition, candidate);
  }
  PUSH_STACK (sweeper->partition, INVALID_LIT);

  LOGBACKBONE ("initialized backbone candidates");
  LOGPARTITION ("initialized equivalence candidates");
}

void Internal::sweep_empty_clause (Sweeper &sweeper) {
  assert (!unsat);
  save_add_clear_core (sweeper);
  assert (unsat);
}

void Internal::sweep_refine_partition (Sweeper &sweeper) {
  kissat *solver = sweeper->solver;
  LOG ("refining partition");
  kitten *kitten = solver->kitten;
  unsigneds old_partition = sweeper->partition;
  unsigneds new_partition;
  INIT_STACK (new_partition);
  const value *const values = solver->values;
  const unsigned *const old_begin = BEGIN_STACK (old_partition);
  const unsigned *const old_end = END_STACK (old_partition);
#ifdef LOGGING
  unsigned old_classes = 0;
  unsigned new_classes = 0;
#endif
  for (const unsigned *p = old_begin, *q; p != old_end; p = q + 1) {
    unsigned assigned_true = 0, other;
    for (q = p; (other = *q) != INVALID_LIT; q++) {
      if (sweep_repr (sweeper, other) != other)
        continue;
      if (values[other])
        continue;
      signed char value = kitten_value (kitten, other);
      if (!value)
        LOG ("dropping sub-solver unassigned %s", LOGLIT (other));
      else if (value > 0) {
        PUSH_STACK (new_partition, other);
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
          POP_STACK (new_partition);
      LOG ("dropping singleton class %s", LOGLIT (other));
    } else {
      LOG ("%u positive literal in class", assigned_true);
      PUSH_STACK (new_partition, INVALID_LIT);
#ifdef LOGGING
      new_classes++;
#endif
    }

    unsigned assigned_false = 0;
    for (q = p; (other = *q) != INVALID_LIT; q++) {
      if (sweep_repr (sweeper, other) != other)
        continue;
      if (values[other])
        continue;
      signed char value = kitten_value (kitten, other);
      if (value < 0) {
        PUSH_STACK (new_partition, other);
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
          POP_STACK (new_partition);
      LOG ("dropping singleton class %s", LOGLIT (other));
    } else {
      LOG ("%u negative literal in class", assigned_false);
      PUSH_STACK (new_partition, INVALID_LIT);
#ifdef LOGGING
      new_classes++;
#endif
    }
  }
  RELEASE_STACK (old_partition);
  sweeper->partition = new_partition;
  LOG ("refined %u classes into %u", old_classes, new_classes);
  LOGPARTITION ("refined equivalence candidates");
}

void Internal::sweep_refine_backbone (Sweeper &sweeper) {
  kissat *solver = sweeper->solver;
  LOG ("refining backbone candidates");
  const unsigned *const end = END_STACK (sweeper->backbone);
  unsigned *q = BEGIN_STACK (sweeper->backbone);
  const value *const values = solver->values;
  kitten *kitten = solver->kitten;
  for (const unsigned *p = q; p != end; p++) {
    const unsigned lit = *p;
    if (values[lit])
      continue;
    signed char value = kitten_value (kitten, lit);
    if (!value)
      LOG ("dropping sub-solver unassigned %s", LOGLIT (lit));
    else if (value >= 0)
      *q++ = lit;
  }
  SET_END_OF_STACK (sweeper->backbone, q);
  LOGBACKBONE ("refined backbone candidates");
}

void Internal::sweep_refine (Sweeper &sweeper) {
#ifdef LOGGING
  kissat *solver = sweeper->solver;
#endif
  if (EMPTY_STACK (sweeper->backbone))
    LOG ("no need to refine empty backbone candidates");
  else
    sweep_refine_backbone (sweeper);
  if (EMPTY_STACK (sweeper->partition))
    LOG ("no need to refine empty partition candidates");
  else
    sweep_refine_partition (sweeper);
}

void Internal::flip_backbone_literals (struct Sweeper &sweeper) {
  struct kissat *solver = sweeper->solver;
  const unsigned max_rounds = opts.sweepfliprounds;
  if (!max_rounds)
    return;
  assert (!EMPTY_STACK (sweeper->backbone));
  struct kitten *kitten = solver->kitten;
  if (kitten_status (kitten) != 10)
    return;
#ifdef LOGGING
  unsigned total_flipped = 0;
#endif
  unsigned flipped, round = 0;
  do {
    round++;
    flipped = 0;
    unsigned *begin = BEGIN_STACK (sweeper->backbone), *q = begin;
    const unsigned *const end = END_STACK (sweeper->backbone), *p = q;
    while (p != end) {
      const unsigned lit = *p++;
      stats.sweep_flip_backbone++;
      if (kitten_flip_literal (kitten, lit)) {
        LOG ("flipping backbone candidate %s succeeded", LOGLIT (lit));
#ifdef LOGGING
        total_flipped++;
#endif
        stats.sweep_flipped_backbone++;
        flipped++;
      } else {
        LOG ("flipping backbone candidate %s failed", LOGLIT (lit));
        *q++ = lit;
      }
    }
    SET_END_OF_STACK (sweeper->backbone, q);
    LOG ("flipped %u backbone candidates in round %u", flipped, round);

    if (terminated_asynchronously ())
      break;
    if (kitten_current_ticks (citten) > sweeper.limit.ticks)
      break;
  } while (flipped && round < max_rounds);
  LOG ("flipped %u backbone candidates in total in %u rounds",
       total_flipped, round);
}

bool Internal::sweep_backbone_candidate (Sweeper &sweeper, unsigned lit) {
  LOG ("trying backbone candidate %d", lit);
  signed char value = kitten_fixed (citten, lit);
  if (value) {
    stats.sweep_fixed_backbone++;
    LOG ("literal %d already fixed", lit);
    assert (value > 0);
    return false;
  }

  stats.sweep_flip_backbone++;
  if (kitten_status (kitten) == 10 && kitten_flip_literal (kitten, lit)) {
    stats.sweep_flipped_backbone++;
    LOG ("flipping %s succeeded", lit);
    LOGBACKBONE ("refined backbone candidates");
    return false;
  }

  LOG ("flipping %s failed", LOGLIT (lit));
  const unsigned not_lit = NOT (lit);
  stats.sweep_solved_backbone++;
  kitten_assume (kitten, not_lit);
  int res = sweep_solve (sweeper);
  if (res == 10) {
    LOG ("sweeping backbone candidate %s failed", LOGLIT (lit));
    sweep_refine (sweeper);
    stats.sweep_sat_backbone++;
    return false;
  }

  if (res == 20) {
    LOG ("sweep unit %s", LOGLIT (lit));
    save_add_clear_core (sweeper);
    stats.sweep_unsat_backbone++;
    return true;
  }

  stats.sweep_unknown_backbone++;

  LOG ("sweeping backbone candidate %s failed", LOGLIT (lit));
  return false;
}

void Internal::add_sweep_binary (int lit, int other) {
  // kissat_new_binary_clause (solver, lit, other);
  // TODO potentially only add for proof -> similar to decompose...
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
    const unsigned last = sweeper->last;
    if (last == 0) {
      assert (sweeper.first == 0);
      sweeper.first = idx;
    } else {
      assert (sweeper.next[last] == 0);
      sweeper.next[last] = idx;
    }
    assert (sweeper->next[idx] == 0);
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

void Internal::substitute_connected_clauses (Sweeper &sweeper, unsigned lit,
                                          unsigned repr) {
  kissat *solver = sweeper->solver;
  if (solver->inconsistent)
    return;
  value *const values = solver->values;
  if (values[lit])
    return;
  if (values[repr])
    return;
  LOG ("substituting %s with %s in all irredundant clauses", LOGLIT (lit),
       LOGLIT (repr));

  assert (lit != repr);
  assert (lit != NOT (repr));

#ifdef CHECKING_OR_PROVING
  const bool checking_or_proving = kissat_checking_or_proving (solver);
  assert (EMPTY_STACK (solver->added));
  assert (EMPTY_STACK (solver->removed));
#endif

  unsigneds *const delayed = &solver->delayed;
  assert (EMPTY_STACK (*delayed));

  {
    watches *lit_watches = &WATCHES (lit);
    watch *const begin_watches = BEGIN_WATCHES (*lit_watches);
    const watch *const end_watches = END_WATCHES (*lit_watches);

    watch *q = begin_watches;
    const watch *p = q;

    while (p != end_watches) {
      const watch head = *q++ = *p++;
      if (head.type.binary) {
        const unsigned other = head.binary.lit;
        const value other_value = values[other];
        if (other == NOT (repr))
          continue;
        if (other_value < 0)
          break;
        if (other_value > 0)
          continue;
        if (other == repr) {
          CHECK_AND_ADD_UNIT (lit);
          ADD_UNIT_TO_PROOF (lit);
          kissat_assign_unit (solver, lit, "substituted binary clause");
          stats.sweep_units++;
          break;
        }
        CHECK_AND_ADD_BINARY (repr, other);
        ADD_BINARY_TO_PROOF (repr, other);
        REMOVE_CHECKER_BINARY (lit, other);
        DELETE_BINARY_FROM_PROOF (lit, other);
        PUSH_STACK (*delayed, head.raw);
        watch src = {.raw = head.raw};
        watch dst = {.raw = head.raw};
        src.binary.lit = lit;
        dst.binary.lit = repr;
        watches *other_watches = &WATCHES (other);
        kissat_substitute_large_watch (solver, other_watches, src, dst);
        q--;
      } else {
        const reference ref = head.large.ref;
        assert (EMPTY_STACK (sweeper->clause));
        clause *c = kissat_dereference_clause (solver, ref);
        if (c->garbage)
          continue;

        bool satisfied = false;
        bool repr_already_watched = false;
        const unsigned not_repr = NOT (repr);
#ifndef NDEBUG
        bool found = false;
#endif
        for (all_literals_in_clause (other, c)) {
          if (other == lit) {
#ifndef NDEBUG
            assert (!found);
            found = true;
#endif
            PUSH_STACK (solver->clause, repr);
            continue;
          }
          assert (other != NOT (lit));
          if (other == repr) {
            assert (!repr_already_watched);
            repr_already_watched = true;
            continue;
          }
          if (other == not_repr) {
            satisfied = true;
            break;
          }
          const value tmp = values[other];
          if (tmp < 0)
            continue;
          if (tmp > 0) {
            satisfied = true;
            break;
          }
          PUSH_STACK (solver->clause, other);
        }

        if (satisfied) {
          CLEAR_STACK (solver->clause);
          kissat_mark_clause_as_garbage (solver, c);
          continue;
        }
        assert (found);

        const unsigned new_size = SIZE_STACK (solver->clause);

        if (new_size == 0) {
          LOGCLS (c, "substituted empty clause");
          assert (!solver->inconsistent);
          solver->inconsistent = true;
          CHECK_AND_ADD_EMPTY ();
          ADD_EMPTY_TO_PROOF ();
          break;
        }

        if (new_size == 1) {
          LOGCLS (c, "reduces to unit");
          const unsigned unit = POP_STACK (solver->clause);
          CHECK_AND_ADD_UNIT (unit);
          ADD_UNIT_TO_PROOF (unit);
          kissat_assign_unit (solver, unit, "substituted large clause");
          stats.sweep_units++;
          break;
        }

        CHECK_AND_ADD_STACK (solver->clause);
        ADD_STACK_TO_PROOF (solver->clause);
        REMOVE_CHECKER_CLAUSE (c);
        DELETE_CLAUSE_FROM_PROOF (c);

        if (!c->redundant)
          kissat_mark_added_literals (solver, new_size,
                                      BEGIN_STACK (solver->clause));

        if (new_size == 2) {
          const unsigned second = POP_STACK (solver->clause);
          const unsigned first = POP_STACK (solver->clause);
          LOGCLS (c, "reduces to binary clause %s %s", LOGLIT (first),
                  LOGLIT (second));
          assert (first == repr || second == repr);
          const unsigned other = first ^ second ^ repr;
          const watch src = {.raw = head.raw};
          watch dst = kissat_binary_watch (repr);
          watches *other_watches = &WATCHES (other);
          kissat_substitute_large_watch (solver, other_watches, src, dst);
          assert (solver->statistics.clauses_irredundant);
          solver->statistics.clauses_irredundant--;
          assert (solver->statistics.clauses_binary < UINT64_MAX);
          solver->statistics.clauses_binary++;
          dst.binary.lit = other;
          PUSH_STACK (*delayed, dst.raw);
          const size_t bytes = kissat_actual_bytes_of_clause (c);
          ADD (arena_garbage, bytes);
          c->garbage = true;
          q--;
          continue;
        }

        assert (2 < new_size);
        const unsigned old_size = c->size;
        assert (new_size <= old_size);

        const unsigned *const begin = BEGIN_STACK (solver->clause);
        const unsigned *const end = END_STACK (solver->clause);

        unsigned *lits = c->lits;
        unsigned *q = lits;

        for (const unsigned *p = begin; p != end; p++) {
          const unsigned other = *p;
          *q++ = other;
        }

        if (new_size < old_size) {
          c->size = new_size;
          c->searched = 2;
          if (c->redundant && c->glue >= new_size)
            kissat_promote_clause (solver, c, new_size - 1);
          if (!c->shrunken) {
            c->shrunken = true;
            lits[old_size - 1] = INVALID_LIT;
          }
        }

        LOGCLS (c, "substituted");

        if (!repr_already_watched)
          PUSH_STACK (*delayed, head.raw);
        CLEAR_STACK (solver->clause);
        q--;
      }
    }
    while (p != end_watches)
      *q++ = *p++;
    SET_END_OF_WATCHES (*lit_watches, q);
  }
  {
    const unsigned *const begin_delayed = BEGIN_STACK (*delayed);
    const unsigned *const end_delayed = END_STACK (*delayed);
    for (const unsigned *p = begin_delayed; p != end_delayed; p++) {
      const watch head = {.raw = *p};
      watches *repr_watches = &WATCHES (repr);
      PUSH_WATCHES (*repr_watches, head);
    }

    CLEAR_STACK (*delayed);
  }

#ifdef CHECKING_OR_PROVING
  if (checking_or_proving) {
    CLEAR_STACK (solver->added);
    CLEAR_STACK (solver->removed);
  }
#endif
}

void Internal::sweep_remove (Sweeper &sweeper, unsigned lit) {
  kissat *solver = sweeper->solver;
  assert (sweeper->reprs[lit] != lit);
  unsigneds *partition = &sweeper->partition;
  unsigned *const begin_partition = BEGIN_STACK (*partition), *p;
  const unsigned *const end_partition = END_STACK (*partition);
  for (p = begin_partition; *p != lit; p++)
    assert (p + 1 != end_partition);
  unsigned *begin_class = p;
  while (begin_class != begin_partition && begin_class[-1] != INVALID_LIT)
    begin_class--;
  const unsigned *end_class = p;
  while (*end_class != INVALID_LIT)
    end_class++;
  const unsigned size = end_class - begin_class;
  LOG ("removing non-representative %s from equivalence class of size %u",
       LOGLIT (lit), size);
  assert (size > 1);
  unsigned *q = begin_class;
  if (size == 2) {
    LOG ("completely squashing equivalence class of %s", LOGLIT (lit));
    for (const unsigned *r = end_class + 1; r != end_partition; r++)
      *q++ = *r;
  } else {
    for (const unsigned *r = begin_class; r != end_partition; r++)
      if (r != p)
        *q++ = *r;
  }
  SET_END_OF_STACK (*partition, q);
#ifndef LOGGING
  (void) solver;
#endif
}

void Internal::flip_partition_literals (struct Sweeper &sweeper) {
  struct kissat *solver = sweeper->solver;
  const unsigned max_rounds = opts.sweepfliprounds;
  if (!max_rounds)
    return;
  assert (!EMPTY_STACK (sweeper->partition));
  struct kitten *kitten = solver->kitten;
  if (kitten_status (kitten) != 10)
    return;
#ifdef LOGGING
  unsigned total_flipped = 0;
#endif
  unsigned flipped, round = 0;
  do {
    round++;
    flipped = 0;
    unsigned *begin = BEGIN_STACK (sweeper->partition), *dst = begin;
    const unsigned *const end = END_STACK (sweeper->partition), *src = dst;
    while (src != end) {
      const unsigned *end_src = src;
      while (assert (end_src != end), *end_src != INVALID_LIT)
        end_src++;
      unsigned size = end_src - src;
      assert (size > 1);
      unsigned *q = dst;
      for (const unsigned *p = src; p != end_src; p++) {
        const unsigned lit = *p;
        if (kitten_flip_literal (kitten, lit)) {
          LOG ("flipping equivalence candidate %s succeeded", LOGLIT (lit));
#ifdef LOGGING
          total_flipped++;
#endif
          flipped++;
          if (--size < 2)
            break;
        } else {
          LOG ("flipping equivalence candidate %s failed", LOGLIT (lit));
          *q++ = lit;
        }
      }
      if (size > 1) {
        *q++ = INVALID_LIT;
        dst = q;
      }
      src = end_src + 1;
    }
    SET_END_OF_STACK (sweeper->partition, dst);
    LOG ("flipped %u equivalence candidates in round %u", flipped, round);

    if (terminated_asynchronously ())
      break;
    if (kitten_current_ticks (citten) > sweeper->limit.ticks)
      break;
  } while (flipped && round < max_rounds);
  LOG ("flipped %u equivalence candidates in total in %u rounds",
       total_flipped, round);
}

bool Internal::sweep_equivalence_candidates (Sweeper &sweeper, unsigned lit,
                                          unsigned other) {
  kissat *solver = sweeper->solver;
  LOG ("trying equivalence candidates %s = %s", LOGLIT (lit),
       LOGLIT (other));
  const unsigned not_other = NOT (other);
  const unsigned not_lit = NOT (lit);
  kitten *kitten = solver->kitten;
  const unsigned *const begin = BEGIN_STACK (sweeper->partition);
  unsigned *const end = END_STACK (sweeper->partition);
  assert (begin + 3 <= end);
  assert (end[-3] == lit);
  assert (end[-2] == other);
  const unsigned third = (end - begin == 3) ? INVALID_LIT : end[-4];
  const int status = kitten_status (kitten);
  if (status == 10 && kitten_flip_literal (kitten, lit)) {
    stats.sweep_flip_equivalences++;
    stats.sweep_flipped_equivalences++;
    LOG ("flipping %s succeeded", LOGLIT (lit));
    if (third == INVALID_LIT) {
      LOG ("squashing equivalence class of %s", LOGLIT (lit));
      SET_END_OF_STACK (sweeper->partition, end - 3);
    } else {
      LOG ("removing %s from equivalence class of %s", LOGLIT (lit),
           LOGLIT (other));
      end[-3] = other;
      end[-2] = INVALID_LIT;
      SET_END_OF_STACK (sweeper->partition, end - 1);
    }
    LOGPARTITION ("refined equivalence candidates");
    return false;
  } else if (status == 10 && kitten_flip_literal (kitten, other)) {
    ADD (sweep_flip_equivalences, 2);
    stats.sweep_flipped_equivalences++;
    LOG ("flipping %s succeeded", LOGLIT (other));
    if (third == INVALID_LIT) {
      LOG ("squashing equivalence class of %s", LOGLIT (lit));
      SET_END_OF_STACK (sweeper->partition, end - 3);
    } else {
      LOG ("removing %s from equivalence class of %s", LOGLIT (other),
           LOGLIT (lit));
      end[-2] = INVALID_LIT;
      SET_END_OF_STACK (sweeper->partition, end - 1);
    }
    LOGPARTITION ("refined equivalence candidates");
    return false;
  }
  if (status == 10)
    ADD (sweep_flip_equivalences, 2);
  LOG ("flipping %s and %s both failed", LOGLIT (lit), LOGLIT (other));
  kitten_assume (kitten, not_lit);
  kitten_assume (kitten, other);
  stats.sweep_solved_equivalences++;
  int res = sweep_solve (sweeper);
  if (res == 10) {
    stats.sweep_sat_equivalences++;
    LOG ("first sweeping implication %s -> %s failed", LOGLIT (other),
         LOGLIT (lit));
    sweep_refine (sweeper);
  } else if (!res) {
    stats.sweep_unknown_equivalences++;
    LOG ("first sweeping implication %s -> %s hit ticks limit",
         LOGLIT (other), LOGLIT (lit));
  }

  if (res != 20)
    return false;

  stats.sweep_unsat_equivalences++;
  LOG ("first sweeping implication %s -> %s succeeded", LOGLIT (other),
       LOGLIT (lit));

  save_core (sweeper, 0);

  kitten_assume (kitten, lit);
  kitten_assume (kitten, not_other);
  res = sweep_solve (sweeper);
  stats.sweep_solved_equivalences++;
  if (res == 10) {
    stats.sweep_sat_equivalences++;
    LOG ("second sweeping implication %s <- %s failed", LOGLIT (other),
         LOGLIT (lit));
    sweep_refine (sweeper);
  } else if (!res) {
    stats.sweep_unknown_equivalences++;
    LOG ("second sweeping implication %s <- %s hit ticks limit",
         LOGLIT (other), LOGLIT (lit));
  }

  if (res != 20) {
    CLEAR_STACK (sweeper->core[0]);
    return false;
  }

  stats.sweep_unsat_equivalences++;
  LOG ("second sweeping implication %s <- %s succeeded too", LOGLIT (other),
       LOGLIT (lit));

  save_core (sweeper, 1);

  LOG ("sweep equivalence %s = %s", LOGLIT (lit), LOGLIT (other));
  stats.sweep_equivalences++;

  add_core (sweeper, 0);
  add_sweep_binary (solver, lit, not_other);
  clear_core (sweeper, 0);

  add_core (sweeper, 1);
  add_sweep_binary (solver, not_lit, other);
  clear_core (sweeper, 1);

  unsigned repr;
  if (lit < other) {
    repr = sweeper->reprs[other] = lit;
    sweeper->reprs[not_other] = not_lit;
    substitute_connected_clauses (sweeper, other, lit);
    substitute_connected_clauses (sweeper, not_other, not_lit);
    sweep_remove (sweeper, other);
  } else {
    repr = sweeper->reprs[lit] = other;
    sweeper->reprs[not_lit] = not_other;
    substitute_connected_clauses (sweeper, lit, other);
    substitute_connected_clauses (sweeper, not_lit, not_other);
    sweep_remove (sweeper, lit);
  }

  const unsigned repr_idx = IDX (repr);
  schedule_inner (sweeper, repr_idx);

  return true;
}

const char *Internal::sweep_variable (Sweeper &sweeper, unsigned idx) {
  kissat *solver = sweeper->solver;
  assert (!solver->inconsistent);
  if (!ACTIVE (idx))
    return "inactive variable";
  const unsigned start = LIT (idx);
  if (sweeper->reprs[start] != start)
    return "non-representative variable";
  assert (EMPTY_STACK (sweeper->vars));
  assert (EMPTY_STACK (sweeper->refs));
  assert (EMPTY_STACK (sweeper->backbone));
  assert (EMPTY_STACK (sweeper->partition));
  assert (!sweeper->encoded);

  stats.sweep_variables++;

  LOG ("sweeping %s", LOGVAR (idx));
  assert (!VALUE (start));
  LOG ("starting sweeping[0]");
  add_literal_to_environment (sweeper, 0, start);
  LOG ("finished sweeping[0]");
  LOG ("starting sweeping[1]");

  bool limit_reached = false;
  size_t expand = 0, next = 1;
  bool success = false;
  unsigned depth = 1;

  while (!limit_reached) {
    if (sweeper->encoded >= sweeper->limit.clauses) {
      LOG ("environment clause limit reached");
      limit_reached = true;
      break;
    }
    if (expand == next) {
      LOG ("finished sweeping[%u]", depth);
      if (depth >= sweeper->limit.depth) {
        LOG ("environment depth limit reached");
        break;
      }
      next = SIZE_STACK (sweeper->vars);
      if (expand == next) {
        LOG ("completely copied all clauses");
        break;
      }
      depth++;
      LOG ("starting sweeping[%u]", depth);
    }
    const unsigned choices = next - expand;
    if (opts.sweeprand && choices > 1) {
      const unsigned swap =
          kissat_pick_random (&solver->random, 0, choices);
      if (swap) {
        unsigned *vars = sweeper->vars.begin;
        SWAP (unsigned, vars[expand], vars[expand + swap]);
      }
    }
    const unsigned idx = PEEK_STACK (sweeper->vars, expand);
    LOG ("traversing and adding clauses of %s", LOGVAR (idx));
    for (unsigned sign = 0; sign < 2; sign++) {
      const unsigned lit = LIT (idx) + sign;
      watches *watches = &WATCHES (lit);
      for (all_binary_large_watches (watch, *watches)) {
        if (watch.type.binary) {
          const unsigned other = watch.binary.lit;
          sweep_binary (sweeper, depth, lit, other);
        } else {
          reference ref = watch.large.ref;
          sweep_reference (sweeper, depth, ref);
        }
        if (SIZE_STACK (sweeper->vars) >= sweeper->limit.vars) {
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
  ADD (sweep_depth, depth);
  ADD (sweep_clauses, sweeper->encoded);
  ADD (sweep_environment, SIZE_STACK (sweeper->vars));
  VERBOSE (3,
                            "sweeping variable %d environment of "
                            "%zu variables %u clauses depth %u",
                            externalize (idx),
                            sweeper.vars.size (), sweeper.encoded,
                            depth);
  int res = sweep_solve (sweeper);
  LOG ("sub-solver returns '%d'", res);
  if (res == 10) {
    init_backbone_and_partition (sweeper);
#ifndef QUIET
    uint64_t units = solver->statistics.sweep_units;
    uint64_t solved = solver->statistics.sweep_solved;
#endif
    START (sweepbackbone);
    while (!EMPTY_STACK (sweeper->backbone)) {
      if (solver->inconsistent || terminated_asynchronously () ||
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
      if (EMPTY_STACK (sweeper->backbone))
        break;
      const unsigned lit = POP_STACK (sweeper->backbone);
      if (!ACTIVE (IDX (lit)))
        continue;
      if (sweep_backbone_candidate (sweeper, lit))
        success = true;
    }
    STOP (sweepbackbone);
#ifndef QUIET
    units = solver->statistics.sweep_units - units;
    solved = solver->statistics.sweep_solved - solved;
#endif
    VERBOSE (
        3,
        "complete swept variable %d backbone with %" PRIu64
        " units in %" PRIu64 " solver calls",
        externalize (idx), units, solved);
    assert (EMPTY_STACK (sweeper->backbone));
#ifndef QUIET
    uint64_t equivalences = solver->statistics.sweep_equivalences;
    solved = solver->statistics.sweep_solved;
#endif
    START (sweepequivalences);
    while (!EMPTY_STACK (sweeper->partition)) {
      if (solver->inconsistent || terminated_asynchronously () ||
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
      if (EMPTY_STACK (sweeper->partition))
        break;
      if (SIZE_STACK (sweeper->partition) > 2) {
        const unsigned *end = END_STACK (sweeper->partition);
        assert (end[-1] == INVALID_LIT);
        unsigned lit = end[-3];
        unsigned other = end[-2];
        if (sweep_equivalence_candidates (sweeper, lit, other))
          success = true;
      } else
        CLEAR_STACK (sweeper->partition);
    }
    STOP (sweepequivalences);
#ifndef QUIET
    equivalences = solver->statistics.sweep_equivalences - equivalences;
    solved = solver->statistics.sweep_solved - solved;
    if (equivalences)
      VERBOSE (
          3,
          "complete swept variable %d partition with %" PRIu64
          " equivalences in %" PRIu64 " solver calls",
          externalize (idx), equivalences, solved);
#endif
  } else if (res == 20)
    sweep_empty_clause (sweeper);

DONE:
  clear_sweeper (sweeper);

  if (!solver->inconsistent && !kissat_propagated (solver))
    (void) kissat_dense_propagate (solver);

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
    if (a.rank < b.rank) return a;
    if (b.rank < a.rank) return b;
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
  kissat *solver = sweeper->solver;
  vector<sweep_candidate> fresh;
  for (const auto & idx : vars) {
    Flags &f = flags (idx);
    if (!f.active)
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
  for (const auto & idx : sweep_schedule)) {
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
    if (!f.active)
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
  VERBOSE (
      3, "retained %u variables %.0f%% to be swept next time",
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
  assert (!solver->unflushed);  // ?
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
    if (stats.kitten_ticks > sweeper.limit.ticks)
      break;
    int idx = next_scheduled (sweeper);
    if (idx == 0)
      break;
    flags (idx).sweep = false;
#ifndef QUIET
    const char *res =
#endif
        sweep_variable (sweeper, idx);
    VERBOSE (
        2, "swept[%" PRIu64 "] external variable %d %s", swept,
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
  PHASE (solver, "sweep", stats.sweep,
                "found %" PRIu64 " equivalences and %" PRIu64 " units",
                equivalences, units);
  unschedule_sweeping (sweeper, swept, scheduled);
  unsigned inactive = release_sweeper (sweeper);

  if (!unsat) {
    propagated = 0;
    if (!propagate ()) {
      learn_empty_clause ();
      unsat = true;
    }
  }

  uint64_t eliminated = equivalences + units;
#ifndef QUIET
  // assert (active () >= inactive);
  // solver->active -= inactive;   // don't know if this is allowed !!
  REPORT (!eliminated, '=');
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
