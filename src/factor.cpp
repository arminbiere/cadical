#include "internal.hpp"

namespace CaDiCaL {

#define FACTORS 1
#define QUOTIENT 2
#define NOUNTED 4

inline bool factor_occs_size::operator() (unsigned a, unsigned b) {
  size_t s = internal->occs (internal->u2i (a)).size ();
  size_t t = internal->occs (internal->u2i (b)).size ();
  if (s > t)
    return true;
  if (s < t)
    return false;
  return a > b;
}

// do full occurence list as in elim.cpp but filter out useless clauses
void Internal::factor_mode () {
  reset_watches ();

  assert (!watching ());
  init_occs ();

  const int size_limit = opts.factorsize;

  vector<unsigned> bincount, largecount;
  const unsigned max_lit = 2 * (max_var + 1);
  enlarge_zero (bincount, max_lit);
  if (size_limit > 2)
    enlarge_zero (largecount, max_lit);

  vector<Clause *> candidates;

  // mark satisfied irredundant clauses as garbage
  for (const auto &c : clauses) {
    if (c->garbage) continue;
    if (c->redundant) continue; // TODO: these? && !c->binary) continue;
    if (c->size > size_limit) continue;
    if (c->size == 2) {
      const int lit = c->literals[0];
      const int other = c->literals[1];
      bincount[vlit (lit)]++;
      bincount[vlit (other)]++;
      occs (vlit (lit)).push_back (c);
      occs (vlit (other)).push_back (c);
      continue;
    }
    candidates.push_back (c);
    for (const auto &lit : *c) {
      largecount[vlit (lit)]++;
    }
  }
  if (size_limit == 2) return;

  const unsigned rounds = opts.factorcandrounds;
  for (unsigned round = 1; round <= rounds; round++) {
    vector<unsigned> newlargecount;
    enlarge_zero (newlargecount, max_lit);
    const auto begin = candidates.begin ();
    auto p = candidates.begin ();
    auto q = p;
    const auto end = candidates.end ();
    while (p != end) {
      Clause *c = *q++ = *p++;
      for (const auto &lit : *c) {
        const auto idx = vlit (lit);
        if (bincount[idx] + largecount[idx] < 2) {
          q--;
          goto CONTINUE_WITH_NEXT_CLAUSE;
        }
      }
      for (const auto &lit : *c) {
        const auto idx = vlit (lit);
        newlargecount[idx]++;
      }
    CONTINUE_WITH_NEXT_CLAUSE:
      continue;
    }
    candidates.resize (q - begin);
    largecount.swap (newlargecount);
  }

  for (const auto &c : candidates) {
    for (const auto &lit : *c) {
      const auto idx = vlit (lit);
      occs (idx).push_back (c);
    }
  }

}

// go back to two watch scheme
void Internal::reset_factor_mode () {
  reset_occs ();
  init_watches ();
  connect_watches ();
}

Factoring::Factoring (Internal *i, int64_t l)
    : internal (i), limit (l), schedule (i) {
  const unsigned max_var = internal->max_var;
  const unsigned max_lit = 2 * (max_var + 1);
  initial = allocated = size = max_var;
  bound = internal->lim.elimbound;
  enlarge_zero (count, max_lit);
  scores = 0;
  quotients.first = quotients.last = 0;
}

Factoring::~Factoring () {
  assert (counted.empty ());
  assert (nounted.empty ());
  assert (flauses.empty ());
  // TODO: scores??
  internal->release_quotients (factoring);
  schedule.erase ();  // actually not necessary
}

double Internal::tied_next_factor_score (int lit) {
  double res = occs (lit).size ();
  LOG ("watches score %g of %d", res, lit);
  return res;
}

// the marks in cadical have 6 bits for marking but work on idx
// to mark everything (FACTORS, QUOTIENT, NOUNTED) we shift the bits
// depending on the sign of factor (+ bitmask)
// i.e. if factor is positive, we apply a bitmask to only get
// the first three bits (& 7u)
// otherwise we leftshift by 3 (>> 3) to get the bits 4,5,6
// use markfact, unmarkfact, getfact for this purpose.
// TODO: check wether we need to mark for multiple things independently...
//
Quotient *Internal::new_quotient (Factoring &factoring, int factor) {
  assert (!getfact (factor, FACTORS));
  markfact (factor, FACTORS);
  Quotient *res = new Quotient (factor);
  res->next = 0;
  res->matched = 0;
  Quotient *last = factoring.quotients.last;
  if (last) {
    assert (factoring.quotients.first);
    assert (!last->next);
    last->next = res;
    res->id = last->id + 1;
  } else {
    assert (!factoring.quotients.first);
    factoring.quotients.first = res;
  }
  factoring.quotients.last = res;
  res->prev = last;
  LOG ("new quotient[%zu] with factor %d", res->id, factor);
  return res;
}


void Internal::release_quotients (Factoring &factoring) {
  for (Quotient *q = factoring.quotients.first, *next; q; q = next) {
    next = q->next;
    int factor = q->factor;
    assert (getfact (factor, FACTORS));
    unmarkfact (factor, FACTORS);
    delete q;
  }
  factoring.quotients.first = factoring.quotients.last = 0;
}

size_t Internal::first_factor (Factoring &factoring, int factor) {
  assert (!factoring.quotients.first);
  Quotient *quotient = new_quotient (factoring, factor);
  vector<Clause *> &qlauses = quotient->qlauses;
  int64_t ticks = 0;
  for (const auto &c : occs (factor)) {
    qlauses.push_back (c);
    ticks++;
  }
  size_t res = qlauses.size ();
  LOG ("quotient[0] factor %d size %zu", factor, res);
  assert (res > 1);
  stats.factor_ticks += ticks;
  return res;
}

void Internal::clear_nounted (vector<int> &nounted) {
  for (const auto &lit : nounted) {
    assert (getfact (lit, NOUNTED));
    unmarkfact (lit, NOUNTED);
  }
  nounted.clear ();
}

void Internal::clear_flauses (vector<Clause *> &flauses) {
  for (auto c : flauses) {
    assert (c->quotient);
    c->quotient = false;
  }
  flauses.clear ();
}

Quotient *Internal::best_quotient (Factoring &factoring,
                                size_t *best_reduction_ptr) {
  size_t factors = 1, best_reduction = 0;
  Quotient *best = 0;
  for (Quotient *q = factoring.quotients.first; q; q = q->next) {
    size_t quotients = q->qlauses.size ();
    size_t before_factorization = quotients * factors;
    size_t after_factorization = quotients + factors;
    if (before_factorization == after_factorization)
      LOG ("quotient[%zu] factors %zu clauses into %zu thus no change",
           factors - 1, before_factorization, after_factorization);
    else if (before_factorization < after_factorization)
      LOG ("quotient[%zu] factors %zu clauses into %zu thus %zu more",
           factors - 1, before_factorization, after_factorization,
           after_factorization - before_factorization);
    else {
      size_t delta = before_factorization - after_factorization;
      LOG ("quotient[%zu] factors %zu clauses into %zu thus %zu less",
           factors - 1, before_factorization, after_factorization, delta);
      if (!best || best_reduction < delta) {
        best_reduction = delta;
        best = q;
      }
    }
    factors++;
  }
  if (!best) {
    LOG ("no decreasing quotient found");
    return 0;
  }
  LOG ("best decreasing quotient[%zu] with reduction %zu", best->id,
       best_reduction);
  *best_reduction_ptr = best_reduction;
  return best;
}

int Internal::next_factor (Factoring &factoring,
                           unsigned *next_count_ptr) {
  Quotient *last_quotient = factoring.quotients.last;
  assert (last_quotient);
  vector<Clause *> &last_clauses = last_quotient->qlauses;
  unsigned &count = factoring.count;
  vector<unsigned> &counted = factoring.counted;
  vector<Clause *> &flauses = &factoring.flauses;
  assert (counted.empty ());
  assert (flauses.empty ());
  const int initial = factoring.initial;
  int64_t ticks = 1; // TODO: + kissat_cache_lines (SIZE_STACK (*last_clauses), sizeof (watch));
  for (auto c : last_clauses) {
    assert (!c->quotient);
    int min_lit = 0;
    unsigned factors = 0;
    size_t min_size = 0;
    ticks++;
    for (const auto &other : *c) {
      if (getfact (other, FACTORS)) {
        if (factors++)
          break;
      } else {
        assert (!getfact (other, QUOTIENT));
        markfact (other, QUOTIENT);
        const size_t other_size = occs (other).size ();
        if (!min_lit || other_size < min_size) {
          min_lit = other;
          min_size = other_size;
        }
      }
    }
    assert (factors);
    if (factors == 1) {
      assert (min_lit);
      const unsigned c_size = c->size;
      vector<unsigned> &nounted = factoring.nounted;
      assert (nounted.empty ());
      ticks += 1; // + kissat_cache_lines (SIZE_WATCHES (*min_watches), sizeof (watch));
      for (auto d : occs (min_lit)) {
        if (c == d) continue;
        ticks++;
        if (d->quotient) continue;
        if (d->size != c_size) continue;
        int next = 0;
        for (const auto &other : *d) {
          if (getmark (other, QUOTIENT))
            continue;
          if (getmark (other, FACTORS))
            goto CONTINUE_WITH_NEXT_MIN_WATCH;
          if (getmark (other, NOUNTED))
            goto CONTINUE_WITH_NEXT_MIN_WATCH;
          if (next)
            goto CONTINUE_WITH_NEXT_MIN_WATCH;
          next = other;
        }
        assert (next);
        if (abs (next) > abs (initial))
          continue;
        if (!active (next))
          continue;
        assert (!getfact (next, FACTORS));
        assert (!getfact (next, NOUNTED));
        markfact (next, NOUNTED);
        nounted.push_back (next);
        d->quotient = true;
        flauses.push_back (d);
        if (!count[vlit (next)])
          counted.push_back (next);
        count[vlit (next)]++;
      CONTINUE_WITH_NEXT_MIN_WATCH:;
      }
      clear_nounted (nounted);
    }
    for (const auto &other : *c)
      if (getfact (other, QUOTIENT))
        unmarkfact (other, QUOTIENT);
    stats.factor_ticks += ticks;
    ticks = 0;
    if (stats.factor_ticks > factoring.limit)
      break;
  }
  clear_flauses (flauses);
  unsigned next_count = 0;
  int next = 0;
  if (stats.factor_ticks <= factoring.limit) {
    unsigned ties = 0;
    for (const auto &lit : counted) {
      const unsigned lit_count = count[vlit (lit)];
      if (lit_count < next_count)
        continue;
      if (lit_count == next_count) {
        assert (lit_count);
        ties++;
      } else {
        assert (lit_count > next_count);
        next_count = lit_count;
        next = lit;
        ties = 1;
      }
    }
    if (next_count < 2) {
      LOG ("next factor count %u smaller than 2", next_count);
      next = 0;
    } else if (ties > 1) {
      LOG ("found %u tied next factor candidate literals with count %u",
           ties, next_count);
      double next_score = -1;
      for (const auto &lit : counted) {
        const unsigned lit_count = count[lit];
        if (lit_count != next_count)
          continue;
        double lit_score = tied_next_factor_score (factoring, lit);
        assert (lit_score >= 0);
        LOG ("score %g of next factor candidate %d", lit_score, lit);
        if (lit_score <= next_score)
          continue;
        next_score = lit_score;
        next = lit;
      }
      assert (next_score >= 0);
      assert (next);
      LOG ("best score %g of next factor %d", next_score, next);
    } else {
      assert (ties == 1);
      LOG ("single next factor %d with count %u", next,
           next_count);
    }
  }
  for (const auto &lit : counted)
    count[vlit (lit)] = 0;
  counted.clear ();
  assert (!next || next_count > 1);
  *next_count_ptr = next_count;
  return next;
}



void Internal::factorize_next (Factoring &factoring, int next,
                              unsigned expected_next_count) {
  Quotient *last_quotient = factoring.quotients.last;
  Quotient *next_quotient = new_quotient (factoring, next);

  assert (last_quotient);
  vector<Clause *> &last_clauses = last_quotient->qlauses;
  vector<Clause *> &next_clauses = next_quotient->qlauses;
  vector<size_t> &matches = next_quotient->matches;
  vector<Clause *> &flauses = factoring.flauses;
  assert (flauses.empty ());

  int64_t ticks = 1;
  //    1 + kissat_cache_lines (SIZE_STACK (*last_clauses), sizeof (watch));

  size_t i = 0;

  for (auto c : last_clauses) {
    assert (!c->quotient);
    int min_lit = 0;
    unsigned factors = 0;
    size_t min_size = 0;
    ticks++;
    for (const auto &other : *c) {
      if (getfact (other, FACTORS)) {
        if (factors++)
          break;
      } else {
        assert (!getfact (other, QUOTIENT));
        markfact (other, QUOTIENT);
        const size_t other_size = occs (other).size ();
        if (!min_lit || other_size < min_size) {
          min_lit = other;
          min_size = other_size;
        }
      }
    }
    assert (factors);
    if (factors == 1) {
      assert (min_lit);
      const unsigned c_size = c->size;
      ticks += 1; //  + kissat_cache_lines (SIZE_STACK (*min_watches),
                 //                      sizeof (watch));
      for (auto d : occs (min_lit)) {
        if (c == d)
          continue;
        ticks++;
        if (d->quotient)
          continue;
        if (d->size != c_size)
          continue;
        for (const auto &other : d) {
          if (getfact (other, QUOTIENT))
            continue;
          if (other != next)
            goto CONTINUE_WITH_NEXT_MIN_WATCH;
        }
        LOG (c, "matched");
        LOG (d, "keeping");
        
        next_clauses.push_back (d);
        matches.push_back (i);
        flauses.push_back (d);
        d->quotient = true;
        break;

      CONTINUE_WITH_NEXT_MIN_WATCH:;
      }
    }
    for (const auto &other : *c)
      if (getfact (other, QUOTIENT))
        unmarkfact (other, QUOTIENT);
    i++;
  }
  clear_flauses (solver, flauses);
  stats.factor_ticks += ticks;

  assert (expected_next_count <= next_clauses.size ());
  (void) expected_next_count;
}

/* kissat code commented below


static void resize_factoring (Factoring &factoring, unsigned lit) {
  kissat *const solver = factoring.solver;
  assert (lit > NOT (lit));
  const size_t old_size = factoring.size;
  assert (lit > old_size);
  const size_t old_allocated = factoring.allocated;
  size_t new_size = lit + 1;
  if (new_size > old_allocated) {
    size_t new_allocated = 2 * old_allocated;
    while (new_size > new_allocated)
      new_allocated *= 2;
    unsigned *count = factoring.count;
    count = kissat_nrealloc (solver, count, old_allocated, new_allocated,
                             sizeof *count);
    const size_t delta_allocated = new_allocated - old_allocated;
    const size_t delta_bytes = delta_allocated * sizeof *count;
    memset (count + old_size, 0, delta_bytes);
    factoring.count = count;
    assert (!(old_allocated & 1));
    assert (!(new_allocated & 1));
    const size_t old_allocated_score = old_allocated / 2;
    const size_t new_allocated_score = new_allocated / 2;
    factoring.allocated = new_allocated;
  }
  factoring.size = new_size;
}

static void flush_unmatched_clauses (kissat *solver, Quotient *q) {
  Quotient *prev = q->prev;
  sizes *q_matches = &q->matches, *prev_matches = &prev->matches;
  statches *q_clauses = &q->clauses, *prev_clauses = &prev->clauses;
  const size_t n = SIZE_STACK (*q_clauses);
  assert (n == SIZE_STACK (*q_matches));
  bool prev_is_first = !prev->id;
  size_t i = 0;
  while (i != n) {
    size_t j = PEEK_STACK (*q_matches, i);
    assert (i <= j);
    if (!prev_is_first) {
      size_t matches = PEEK_STACK (*prev_matches, j);
      POKE_STACK (*prev_matches, i, matches);
    }
    watch watch = PEEK_STACK (*prev_clauses, j);
    POKE_STACK (*prev_clauses, i, watch);
    i++;
  }
  LOG ("flushing %zu clauses of quotient[%zu]",
       SIZE_STACK (*prev_clauses) - n, prev->id);
  if (!prev_is_first)
    RESIZE_STACK (*prev_matches, n);
  RESIZE_STACK (*prev_clauses, n);
  (void) solver;
}

static void add_factored_divider (Factoring &factoring, Quotient *q,
                                  unsigned fresh) {
  const unsigned factor = q->factor;
  kissat *const solver = factoring.solver;
  LOGBINARY (fresh, factor, "factored %s divider", LOGLIT (factor));
  kissat_new_binary_clause (solver, fresh, factor);
  INC (clauses_factored);
  ADD (literals_factored, 2);
}

static void add_factored_quotient (Factoring &factoring, Quotient *q,
                                   unsigned not_fresh) {
  kissat *const solver = factoring.solver;
  LOG ("adding factored quotient[%zu] clauses", q->id);
  for (all_stack (watch, watch, q->clauses)) {
    if (watch.type.binary) {
      const unsigned other = watch.binary.lit;
      LOGBINARY (not_fresh, other, "factored quotient");
      kissat_new_binary_clause (solver, not_fresh, other);
      ADD (literals_factored, 2);
    } else {
      const reference c_ref = watch.large.ref;
      clause *const c = kissat_dereference_clause (solver, c_ref);
      unsigneds *clause = &solver->clause;
      assert (EMPTY_STACK (*clause));
      const unsigned factor = q->factor;
#ifndef NDEBUG
      bool found = false;
#endif
      PUSH_STACK (*clause, not_fresh);
      for (all_literals_in_clause (other, c)) {
        if (other == factor) {
#ifndef NDEBUG
          found = true;
#endif
          continue;
        }
        PUSH_STACK (*clause, other);
      }
      assert (found);
      ADD (literals_factored, c->size);
      kissat_new_irredundant_clause (solver);
      CLEAR_STACK (*clause);
    }
    INC (clauses_factored);
  }
}

static void eagerly_remove_watch (kissat *solver, watches *watches,
                                  watch needle) {
  watch *p = BEGIN_WATCHES (*watches);
  watch *end = END_WATCHES (*watches);
  assert (p != end);
  watch *last = end - 1;
  while (p->raw != needle.raw)
    p++, assert (p != end);
  if (p != last)
    memmove (p, p + 1, (last - p) * sizeof *p);
  SET_END_OF_WATCHES (*watches, last);
}

static void eagerly_remove_binary (kissat *solver, watches *watches,
                                   unsigned lit) {
  const watch needle = kissat_binary_watch (lit);
  eagerly_remove_watch (solver, watches, needle);
}

static void delete_unfactored (Factoring &factoring, Quotient *q) {
  kissat *const solver = factoring.solver;
  LOG ("deleting unfactored quotient[%zu] clauses", q->id);
  const unsigned factor = q->factor;
  for (all_stack (watch, watch, q->clauses)) {
    if (watch.type.binary) {
      const unsigned other = watch.binary.lit;
      LOGBINARY (factor, other, "deleting unfactored");
      eagerly_remove_binary (solver, &WATCHES (other), factor);
      eagerly_remove_binary (solver, &WATCHES (factor), other);
      kissat_delete_binary (solver, factor, other);
      ADD (literals_unfactored, 2);
    } else {
      const reference ref = watch.large.ref;
      clause *c = kissat_dereference_clause (solver, ref);
      LOGCLS (c, "deleting unfactored");
      for (all_literals_in_clause (lit, c))
        eagerly_remove_watch (solver, &WATCHES (lit), watch);
      kissat_mark_clause_as_garbage (solver, c);
      ADD (literals_unfactored, c->size);
    }
    INC (clauses_unfactored);
  }
}

static void update_factored (Factoring &factoring, Quotient *q) {
  kissat *const solver = factoring.solver;
  const unsigned factor = q->factor;
  update_factor_candidate (factoring, factor);
  update_factor_candidate (factoring, NOT (factor));
  for (all_stack (watch, watch, q->clauses)) {
    if (watch.type.binary) {
      const unsigned other = watch.binary.lit;
      update_factor_candidate (factoring, other);
    } else {
      const reference ref = watch.large.ref;
      clause *c = kissat_dereference_clause (solver, ref);
      LOGCLS (c, "deleting unfactored");
      for (all_literals_in_clause (lit, c))
        if (lit != factor)
          update_factor_candidate (factoring, lit);
    }
  }
}

static bool apply_factoring (Factoring &factoring, Quotient *q) {
  kissat *const solver = factoring.solver;
  const unsigned fresh = kissat_fresh_literal (solver);
  if (fresh == INVALID_LIT)
    return false;
  INC (factored);
  PUSH_STACK (factoring.fresh, fresh);
  for (Quotient *p = q; p->prev; p = p->prev)
    flush_unmatched_clauses (solver, p);
  for (Quotient *p = q; p; p = p->prev)
    add_factored_divider (factoring, p, fresh);
  const unsigned not_fresh = NOT (fresh);
  add_factored_quotient (factoring, q, not_fresh);
  for (Quotient *p = q; p; p = p->prev)
    delete_unfactored (factoring, p);
  for (Quotient *p = q; p; p = p->prev)
    update_factored (factoring, p);
  assert (fresh < not_fresh);
  resize_factoring (factoring, not_fresh);
  return true;
}

above is kissat code
*/


void Internal::update_factor_candidate (Factoring &factoring, int lit) {
  FactorSchedule &schedule = factoring.schedule;
  const size_t size = occs (lit).size ();
  const unsigned idx = vlit (lit);
  if (schedule.contains (idx))
    schedule.update (idx);
  else if (size > 1) {
    schedule.push_back (idx);
  }
}


void Internal::schedule_factorization (Factoring &factoring) {
  for (const auto &idx : vars) {
    if (active (idx)) {
      Flags &f = flags (idx);
      const int lit = idx;
      const int not_lit = -lit;
      if (f.factor & 1)
        update_factor_candidate (factoring, lit);
      if (f.factor & 2)
        update_factor_candidate (factoring, not_lit);
    }
  }
#ifndef QUIET
  size_t size_cands = factoring.schedule.size ();
  VERBOSE (2, "scheduled %zu factorization candidate literals %.0f %%",
      size_cands, percent (size_cands, max_var));
#endif
}

bool Internal::run_factorization (int64_t limit) {
  Factoring factoring = Factoring (this, limit); // TODO new or not new
  schedule_factorization (factoring);
  bool done = false;
#ifndef QUIET
  unsigned factored = 0;
#endif
  int64_t *ticks = &stats.factor_ticks;
  VERBOSE (3, "factorization limit of %" PRIu64 " ticks", limit - *ticks);

  while (!done && !factoring.schedule.empty ()) {
    const unsigned ufirst = factoring.schedule.pop_front ();
    const int first = u2i (ufirst);
    const int first_idx = vidx (first);
    if (!active (first_idx))
      continue;
    if (!occs (first).size ()) {
      factoring.schedule.clear ();
      break;
    }
    if (*ticks > limit) {
      VERBOSE (2, "factorization ticks limit hit");
      break;
    }
    if (terminated_asynchronously ())
      break;
    Flags &f = flags (first_idx);
    const unsigned bit = 1u << (first < 0);
    if (!(f->factor & bit))
      continue;
    f->factor &= ~bit;
    const size_t first_count = first_factor (factoring, first);
    if (first_count > 1) {
      for (;;) {
        unsigned next_count;
        const int next = next_factor (factoring, &next_count);
        if (next == 0)
          break;
        assert (next_count > 1);
        if (next_count < 2)
          break;
        factorize_next (factoring, next, next_count);
      }
      size_t reduction;
      Quotient *q = best_quotient (factoring, &reduction);
      if (q && reduction > factoring.bound) {
        if (apply_factoring (factoring, q)) {
          factored++;
        } else
          done = true;
      }
    }
    release_quotients (factoring);
  }
  
  // since we cannot remove elements from the heap we check wether the
  // first element in the heap has occurences
  bool completed = factoring.schedule.empty ();
  if (!completed) {
    const unsigned idx = factoring.schedule.front ();
    completed = occs (u2i (idx)).empty ();
  }
  // kissat initializes scores for new variables at this point, however
  // this is actually done already during resize of internal
  report ('f', !factored);
  // TODO: if factoring is not pointer it should automatically
  // call destructor upon leaving this function??
  // delete factoring;
  return completed;
}

int Internal::get_new_extension_variable () {
  const int current_max_external = external->max_var;
  const int new_external = current_max_external + 1;
  const int new_internal = external->internalize (new_external, true);
  return new_internal;
}

void Internal::factor () {
  if (unsat)
    return;
  if (terminated_asynchronously ())
    return;
  if (!opts.factor)
    return;
  if (last.factor.marked >= stats.factor_literals) {
    VERBOSE (3, "factorization skipped as no literals have been"
        "marked to be added (%" PRIu64 " < %" PRIu64 ")",
        last.factor.marked, stats.factor_literals);
    return;
  }
  assert (!level);
  START_SIMPLIFIER (factor, FACTOR);
  stats.factor++;

  int64_t limit = opts.factoriniticks;
  if (stats.factor > 1) {
    int64_t tmp = stats.propagations.search - last.factor.ticks;
    tmp *= opts.factoreffort;
    limit = tmp;
  } else {
    VERBOSE (3, "initially limiting to %" PRIu64
               " million factorization ticks",
               limit);
    limit *= 1e6;
    limit += stats.factor_ticks;
  }

  // TODO commented code for messages
  /*
  struct {
    int64_t variables, clauses, ticks;
  } before, after, delta;
  before.variables = stats.variables_extension + stats.variables_original;
  before.ticks = stats.factor_ticks;
  */
  factor_mode ();
  bool completed = run_factorization (limit);
  reset_factor_mode ();

  /*
  after.variables = s->variables_extension + s->variables_original;
  after.binary = BINARY_CLAUSES;
  after.clauses = IRREDUNDANT_CLAUSES;
  after.ticks = s->factor_ticks;
  delta.variables = after.variables - before.variables;
  delta.binary = before.binary - after.binary;
  delta.clauses = before.clauses - after.clauses;
  delta.ticks = after.ticks - before.ticks;
  kissat_very_verbose (solver, "used %f million factorization ticks",
                       delta.ticks * 1e-6);
  kissat_phase (solver, "factorization", GET (factorizations),
                "introduced %" PRId64 " extension variables %.0f%%",
                delta.variables,
                kissat_percent (delta.variables, before.variables));
  kissat_phase (solver, "factorization", GET (factorizations),
                "removed %" PRId64 " binary clauses %.0f%%", delta.binary,
                kissat_percent (delta.binary, before.binary));
  kissat_phase (solver, "factorization", GET (factorizations),
                "removed %" PRId64 " large clauses %.0f%%", delta.clauses,
                kissat_percent (delta.clauses, before.clauses));

  VERBOSE (2, "factored %" PRIu64 " new variables", factored);
  VERBOSE (2, "factorization added %" PRIu64 " and deleted %" PRIu64 " clauses", added, deleted);
  */
  if (completed)
    last.factor.marked = stats.factor_literals;
  STOP_SIMPLIFIER (factor, FACTOR);
}

}