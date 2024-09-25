#include "internal.hpp"

namespace CaDiCaL {

#define FACTOR 1
#define QUOTIENT 2
#define NOUNTED 4

void Internal::init_factoring (Factoring *factoring, uint64_t limit) {
  memset (factoring, 0, sizeof *factoring);
  factoring->initial = factoring->allocated = factoring->size = LITS;
  factoring->limit = limit;
  factoring->bound = solver->bounds.eliminate.additional_clauses;
  CALLOC (factoring->count, factoring->allocated);
#ifndef NDEBUG
  for (all_literals (lit))
    assert (!solver->marks[lit]);
#endif
}

static void release_quotients (Factoring *factoring) {
  kissat *const solver = factoring->solver;
  mark *marks = solver->marks;
  for (quotient *q = factoring->quotients.first, *next; q; q = next) {
    next = q->next;
    unsigned factor = q->factor;
    assert (marks[factor] == FACTOR);
    marks[factor] = 0;
    RELEASE_STACK (q->clauses);
    RELEASE_STACK (q->matches);
    kissat_free (solver, q, sizeof *q);
  }
  factoring->quotients.first = factoring->quotients.last = 0;
}

static void release_factoring (Factoring *factoring) {
  kissat *const solver = factoring->solver;
  assert (EMPTY_STACK (solver->analyzed));
  assert (EMPTY_STACK (factoring->counted));
  assert (EMPTY_STACK (factoring->nounted));
  assert (EMPTY_STACK (factoring->qlauses));
  DEALLOC (factoring->count, factoring->allocated);
  RELEASE_STACK (factoring->counted);
  RELEASE_STACK (factoring->nounted);
  RELEASE_STACK (factoring->fresh);
  RELEASE_STACK (factoring->qlauses);
  release_quotients (factoring);
  kissat_release_heap (solver, &factoring->schedule);
  assert (!(factoring->allocated & 1));
  const size_t allocated_score = factoring->allocated / 2;
#ifndef NDEBUG
  for (all_literals (lit))
    assert (!solver->marks[lit]);
#endif
}

static void update_candidate (Factoring *factoring, unsigned lit) {
  heap *cands = &factoring->schedule;
  kissat *const solver = factoring->solver;
  const size_t size = SIZE_WATCHES (solver->watches[lit]);
  if (size > 1) {
    kissat_adjust_heap (solver, cands, lit);
    kissat_update_heap (solver, cands, lit, size);
    if (!kissat_heap_contains (cands, lit))
      kissat_push_heap (solver, cands, lit);
  } else if (kissat_heap_contains (cands, lit))
    kissat_pop_heap (solver, cands, lit);
}

static void schedule_factorization (Factoring *factoring) {
  kissat *const solver = factoring->solver;
  flags *flags = solver->flags;
  for (all_variables (idx)) {
    if (ACTIVE (idx)) {
      struct flags *f = flags + idx;
      const unsigned lit = LIT (idx);
      const unsigned not_lit = NOT (lit);
      if (f->factor & 1)
        update_candidate (factoring, lit);
      if (f->factor & 2)
        update_candidate (factoring, not_lit);
    }
  }
#ifndef QUIET
  heap *cands = &factoring->schedule;
  size_t size_cands = kissat_size_heap (cands);
  kissat_very_verbose (
      solver, "scheduled %zu factorization candidate literals %.0f %%",
      size_cands, kissat_percent (size_cands, LITS));
#endif
}

static quotient *new_quotient (Factoring *factoring, unsigned factor) {
  kissat *const solver = factoring->solver;
  mark *marks = solver->marks;
  assert (!marks[factor]);
  marks[factor] = FACTOR;
  quotient *res = kissat_malloc (solver, sizeof *res);
  memset (res, 0, sizeof *res);
  res->factor = factor;
  quotient *last = factoring->quotients.last;
  if (last) {
    assert (factoring->quotients.first);
    assert (!last->next);
    last->next = res;
    res->id = last->id + 1;
  } else {
    assert (!factoring->quotients.first);
    factoring->quotients.first = res;
  }
  factoring->quotients.last = res;
  res->prev = last;
  LOG ("new quotient[%zu] with factor %s", res->id, LOGLIT (factor));
  return res;
}

static size_t first_factor (Factoring *factoring, unsigned factor) {
  kissat *const solver = factoring->solver;
  watches *all_watches = solver->watches;
  watches *factor_watches = all_watches + factor;
  assert (!factoring->quotients.first);
  quotient *quotient = new_quotient (factoring, factor);
  statches *clauses = &quotient->clauses;
  uint64_t ticks = 0;
  for (all_binary_large_watches (watch, *factor_watches)) {
    PUSH_STACK (*clauses, watch);
#ifndef NDEBUG
    if (watch.type.binary)
      continue;
    const reference ref = watch.large.ref;
    clause *const c = kissat_dereference_clause (solver, ref);
    assert (!c->quotient);
#endif
    ticks++;
  }
  size_t res = SIZE_STACK (*clauses);
  LOG ("quotient[0] factor %s size %zu", LOGLIT (factor), res);
  assert (res > 1);
  ADD (factor_ticks, ticks);
  return res;
}

static void clear_nounted (kissat *solver, unsigneds *nounted) {
  mark *marks = solver->marks;
  for (all_stack (unsigned, lit, *nounted)) {
    assert (marks[lit] & NOUNTED);
    marks[lit] &= ~NOUNTED;
  }
  CLEAR_STACK (*nounted);
}

static void clear_qlauses (kissat *solver, references *qlauses) {
  ward *const arena = BEGIN_STACK (solver->arena);
  for (all_stack (reference, ref, *qlauses)) {
    clause *const c = (clause *) (arena + ref);
    assert (c->quotient);
    c->quotient = false;
  }
  CLEAR_STACK (*qlauses);
}

static double tied_next_factor_score (Factoring *factoring, unsigned lit) {
  kissat *const solver = factoring->solver;
  watches *watches = solver->watches + lit;
  double res = SIZE_WATCHES (*watches);
  LOG ("watches score %g of %s", res, LOGLIT (lit));
  return res;
}

static unsigned next_factor (Factoring *factoring,
                             unsigned *next_count_ptr) {
  quotient *last_quotient = factoring->quotients.last;
  assert (last_quotient);
  statches *last_clauses = &last_quotient->clauses;
  kissat *const solver = factoring->solver;
  watches *all_watches = solver->watches;
  unsigned *count = factoring->count;
  unsigneds *counted = &factoring->counted;
  references *qlauses = &factoring->qlauses;
  assert (EMPTY_STACK (*counted));
  assert (EMPTY_STACK (*qlauses));
  ward *const arena = BEGIN_STACK (solver->arena);
  mark *marks = solver->marks;
  const unsigned initial = factoring->initial;
  uint64_t ticks =
      1 + kissat_cache_lines (SIZE_STACK (*last_clauses), sizeof (watch));
  for (all_stack (watch, quotient_watch, *last_clauses)) {
    if (quotient_watch.type.binary) {
      const unsigned q = quotient_watch.binary.lit;
      watches *q_watches = all_watches + q;
      ticks += 1 + kissat_cache_lines (SIZE_WATCHES (*q_watches),
                                       sizeof (watch));
      for (all_binary_large_watches (next_watch, *q_watches)) {
        if (!next_watch.type.binary)
          continue;
        const unsigned next = next_watch.binary.lit;
        if (next > initial)
          continue;
        if (marks[next] & FACTOR)
          continue;
        const unsigned next_idx = IDX (next);
        if (!ACTIVE (next_idx))
          continue;
        if (!count[next])
          PUSH_STACK (*counted, next);
        count[next]++;
      }
    } else {
      const reference c_ref = quotient_watch.large.ref;
      clause *const c = (clause *) (arena + c_ref);
      assert (!c->quotient);
      unsigned min_lit = INVALID_LIT, factors = 0;
      size_t min_size = 0;
      ticks++;
      for (all_literals_in_clause (other, c)) {
        if (marks[other] & FACTOR) {
          if (factors++)
            break;
        } else {
          assert (!(marks[other] & QUOTIENT));
          marks[other] |= QUOTIENT;
          watches *other_watches = all_watches + other;
          const size_t other_size = SIZE_WATCHES (*other_watches);
          if (min_lit != INVALID_LIT && min_size <= other_size)
            continue;
          min_lit = other;
          min_size = other_size;
        }
      }
      assert (factors);
      if (factors == 1) {
        assert (min_lit != INVALID_LIT);
        watches *min_watches = all_watches + min_lit;
        unsigned c_size = c->size;
        unsigneds *nounted = &factoring->nounted;
        assert (EMPTY_STACK (*nounted));
        ticks += 1 + kissat_cache_lines (SIZE_WATCHES (*min_watches),
                                         sizeof (watch));
        for (all_binary_large_watches (min_watch, *min_watches)) {
          if (min_watch.type.binary)
            continue;
          const reference d_ref = min_watch.large.ref;
          if (c_ref == d_ref)
            continue;
          clause *const d = (clause *) (arena + d_ref);
          ticks++;
          if (d->quotient)
            continue;
          if (d->size != c_size)
            continue;
          unsigned next = INVALID_LIT;
          for (all_literals_in_clause (other, d)) {
            const mark mark = marks[other];
            if (mark & QUOTIENT)
              continue;
            if (mark & FACTOR)
              goto CONTINUE_WITH_NEXT_MIN_WATCH;
            if (mark & NOUNTED)
              goto CONTINUE_WITH_NEXT_MIN_WATCH;
            if (next != INVALID_LIT)
              goto CONTINUE_WITH_NEXT_MIN_WATCH;
            next = other;
          }
          assert (next != INVALID_LIT);
          if (next > initial)
            continue;
          const unsigned next_idx = IDX (next);
          if (!ACTIVE (next_idx))
            continue;
          assert (!(marks[next] & (FACTOR | NOUNTED)));
          marks[next] |= NOUNTED;
          PUSH_STACK (*nounted, next);
          d->quotient = true;
          PUSH_STACK (*qlauses, d_ref);
          if (!count[next])
            PUSH_STACK (*counted, next);
          count[next]++;
        CONTINUE_WITH_NEXT_MIN_WATCH:;
        }
        clear_nounted (solver, nounted);
      }
      for (all_literals_in_clause (other, c))
        marks[other] &= ~QUOTIENT;
    }
    ADD (factor_ticks, ticks);
    ticks = 0;
    if (solver->statistics.factor_ticks > factoring->limit)
      break;
  }
  clear_qlauses (solver, qlauses);
  unsigned next_count = 0, next = INVALID_LIT;
  if (solver->statistics.factor_ticks <= factoring->limit) {
    unsigned ties = 0;
    for (all_stack (unsigned, lit, *counted)) {
      const unsigned lit_count = count[lit];
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
      next = INVALID_LIT;
    } else if (ties > 1) {
      LOG ("found %u tied next factor candidate literals with count %u",
           ties, next_count);
      double next_score = -1;
      for (all_stack (unsigned, lit, *counted)) {
        const unsigned lit_count = count[lit];
        if (lit_count != next_count)
          continue;
        double lit_score = tied_next_factor_score (factoring, lit);
        assert (lit_score >= 0);
        LOG ("score %g of next factor candidate %s", lit_score,
             LOGLIT (lit));
        if (lit_score <= next_score)
          continue;
        next_score = lit_score;
        next = lit;
      }
      assert (next_score >= 0);
      assert (next != INVALID_LIT);
      LOG ("best score %g of next factor %s", next_score, LOGLIT (next));
    } else {
      assert (ties == 1);
      LOG ("single next factor %s with count %u", LOGLIT (next),
           next_count);
    }
  }
  for (all_stack (unsigned, lit, *counted))
    count[lit] = 0;
  CLEAR_STACK (*counted);
  assert (next == INVALID_LIT || next_count > 1);
  *next_count_ptr = next_count;
  return next;
}

static void factorize_next (Factoring *factoring, unsigned next,
                            unsigned expected_next_count) {
  quotient *last_quotient = factoring->quotients.last;
  quotient *next_quotient = new_quotient (factoring, next);

  kissat *const solver = factoring->solver;
  watches *all_watches = solver->watches;
  ward *const arena = BEGIN_STACK (solver->arena);
  mark *marks = solver->marks;

  assert (last_quotient);
  statches *last_clauses = &last_quotient->clauses;
  statches *next_clauses = &next_quotient->clauses;
  sizes *matches = &next_quotient->matches;
  references *qlauses = &factoring->qlauses;
  assert (EMPTY_STACK (*qlauses));

  uint64_t ticks =
      1 + kissat_cache_lines (SIZE_STACK (*last_clauses), sizeof (watch));

  size_t i = 0;

  for (all_stack (watch, last_watch, *last_clauses)) {
    if (last_watch.type.binary) {
      const unsigned q = last_watch.binary.lit;
      watches *q_watches = all_watches + q;
      ticks += 1 + kissat_cache_lines (SIZE_WATCHES (*q_watches),
                                       sizeof (watch));
      for (all_binary_large_watches (q_watch, *q_watches))
        if (q_watch.type.binary && q_watch.binary.lit == next) {
          LOGBINARY (last_quotient->factor, q, "matched");
          LOGBINARY (next, q, "keeping");
          PUSH_STACK (*next_clauses, last_watch);
          PUSH_STACK (*matches, i);
          break;
        }
    } else {
      const reference c_ref = last_watch.large.ref;
      clause *const c = (clause *) (arena + c_ref);
      assert (!c->quotient);
      unsigned min_lit = INVALID_LIT, factors = 0;
      size_t min_size = 0;
      ticks++;
      for (all_literals_in_clause (other, c)) {
        if (marks[other] & FACTOR) {
          if (factors++)
            break;
        } else {
          assert (!(marks[other] & QUOTIENT));
          marks[other] |= QUOTIENT;
          watches *other_watches = all_watches + other;
          const size_t other_size = SIZE_WATCHES (*other_watches);
          if (min_lit != INVALID_LIT && min_size <= other_size)
            continue;
          min_lit = other;
          min_size = other_size;
        }
      }
      assert (factors);
      if (factors == 1) {
        assert (min_lit != INVALID_LIT);
        watches *min_watches = all_watches + min_lit;
        unsigned c_size = c->size;
        ticks += 1 + kissat_cache_lines (SIZE_STACK (*min_watches),
                                         sizeof (watch));
        for (all_binary_large_watches (min_watch, *min_watches)) {
          if (min_watch.type.binary)
            continue;
          const reference d_ref = min_watch.large.ref;
          if (c_ref == d_ref)
            continue;
          clause *const d = (clause *) (arena + d_ref);
          ticks++;
          if (d->quotient)
            continue;
          if (d->size != c_size)
            continue;
          for (all_literals_in_clause (other, d)) {
            const mark mark = marks[other];
            if (mark & QUOTIENT)
              continue;
            if (other != next)
              goto CONTINUE_WITH_NEXT_MIN_WATCH;
          }
          LOGCLS (c, "matched");
          LOGCLS (d, "keeping");
          PUSH_STACK (*next_clauses, min_watch);
          PUSH_STACK (*matches, i);
          PUSH_STACK (*qlauses, d_ref);
          d->quotient = true;
          break;
        CONTINUE_WITH_NEXT_MIN_WATCH:;
        }
      }
      for (all_literals_in_clause (other, c))
        marks[other] &= ~QUOTIENT;
    }
    i++;
  }

  clear_qlauses (solver, qlauses);
  ADD (factor_ticks, ticks);

  assert (expected_next_count <= SIZE_STACK (*next_clauses));
  (void) expected_next_count;
}

static quotient *best_quotient (Factoring *factoring,
                                size_t *best_reduction_ptr) {
  size_t factors = 1, best_reduction = 0;
  quotient *best = 0;
  kissat *const solver = factoring->solver;
  for (quotient *q = factoring->quotients.first; q; q = q->next) {
    size_t quotients = SIZE_STACK (q->clauses);
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
  (void) solver;
  return best;
}

static void resize_factoring (Factoring *factoring, unsigned lit) {
  kissat *const solver = factoring->solver;
  assert (lit > NOT (lit));
  const size_t old_size = factoring->size;
  assert (lit > old_size);
  const size_t old_allocated = factoring->allocated;
  size_t new_size = lit + 1;
  if (new_size > old_allocated) {
    size_t new_allocated = 2 * old_allocated;
    while (new_size > new_allocated)
      new_allocated *= 2;
    unsigned *count = factoring->count;
    count = kissat_nrealloc (solver, count, old_allocated, new_allocated,
                             sizeof *count);
    const size_t delta_allocated = new_allocated - old_allocated;
    const size_t delta_bytes = delta_allocated * sizeof *count;
    memset (count + old_size, 0, delta_bytes);
    factoring->count = count;
    assert (!(old_allocated & 1));
    assert (!(new_allocated & 1));
    const size_t old_allocated_score = old_allocated / 2;
    const size_t new_allocated_score = new_allocated / 2;
    factoring->allocated = new_allocated;
  }
  factoring->size = new_size;
}

static void flush_unmatched_clauses (kissat *solver, quotient *q) {
  quotient *prev = q->prev;
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

static void add_factored_divider (Factoring *factoring, quotient *q,
                                  unsigned fresh) {
  const unsigned factor = q->factor;
  kissat *const solver = factoring->solver;
  LOGBINARY (fresh, factor, "factored %s divider", LOGLIT (factor));
  kissat_new_binary_clause (solver, fresh, factor);
  INC (clauses_factored);
  ADD (literals_factored, 2);
}

static void add_factored_quotient (Factoring *factoring, quotient *q,
                                   unsigned not_fresh) {
  kissat *const solver = factoring->solver;
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

static void delete_unfactored (Factoring *factoring, quotient *q) {
  kissat *const solver = factoring->solver;
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

static void update_factored (Factoring *factoring, quotient *q) {
  kissat *const solver = factoring->solver;
  const unsigned factor = q->factor;
  update_candidate (factoring, factor);
  update_candidate (factoring, NOT (factor));
  for (all_stack (watch, watch, q->clauses)) {
    if (watch.type.binary) {
      const unsigned other = watch.binary.lit;
      update_candidate (factoring, other);
    } else {
      const reference ref = watch.large.ref;
      clause *c = kissat_dereference_clause (solver, ref);
      LOGCLS (c, "deleting unfactored");
      for (all_literals_in_clause (lit, c))
        if (lit != factor)
          update_candidate (factoring, lit);
    }
  }
}

static bool apply_factoring (Factoring *factoring, quotient *q) {
  kissat *const solver = factoring->solver;
  const unsigned fresh = kissat_fresh_literal (solver);
  if (fresh == INVALID_LIT)
    return false;
  INC (factored);
  PUSH_STACK (factoring->fresh, fresh);
  for (quotient *p = q; p->prev; p = p->prev)
    flush_unmatched_clauses (solver, p);
  for (quotient *p = q; p; p = p->prev)
    add_factored_divider (factoring, p, fresh);
  const unsigned not_fresh = NOT (fresh);
  add_factored_quotient (factoring, q, not_fresh);
  for (quotient *p = q; p; p = p->prev)
    delete_unfactored (factoring, p);
  for (quotient *p = q; p; p = p->prev)
    update_factored (factoring, p);
  assert (fresh < not_fresh);
  resize_factoring (factoring, not_fresh);
  return true;
}

static void
adjust_scores_and_phases_of_fresh_varaibles (Factoring *factoring) {
  const unsigned *begin = BEGIN_STACK (factoring->fresh);
  const unsigned *end = END_STACK (factoring->fresh);
  kissat *const solver = factoring->solver;
  {
    const unsigned *p = begin;
    while (p != end) {
      const unsigned lit = *p++;
      const unsigned idx = IDX (lit);
      LOG ("unbumping fresh[%zu] %s", (size_t) (p - begin - 1),
           LOGVAR (idx));
      const double score = 0;
      kissat_update_heap (solver, &solver->scores, idx, score);
    }
  }
  {
    const unsigned *p = end;
    links *links = solver->links;
    queue *queue = &solver->queue;
    while (p != begin) {
      const unsigned lit = *--p;
      const unsigned idx = IDX (lit);
      kissat_dequeue_links (idx, links, queue);
    }
    queue->stamp = 0;
    unsigned rest = queue->first;
    p = end;
    while (p != begin) {
      const unsigned lit = *--p;
      const unsigned idx = IDX (lit);
      struct links *l = links + idx;
      if (DISCONNECTED (queue->first)) {
        assert (DISCONNECTED (queue->last));
        queue->last = idx;
      } else {
        struct links *first = links + queue->first;
        assert (DISCONNECTED (first->prev));
        first->prev = idx;
      }
      l->next = queue->first;
      queue->first = idx;
      assert (DISCONNECTED (l->prev));
      l->stamp = ++queue->stamp;
    }
    while (!DISCONNECTED (rest)) {
      struct links *l = links + rest;
      l->stamp = ++queue->stamp;
      rest = l->next;
    }
    solver->queue.search.idx = queue->last;
    solver->queue.search.stamp = queue->stamp;
  }
}

static bool run_factorization (kissat *solver, uint64_t limit) {
  factoring factoring;
  init_factoring (solver, &factoring, limit);
  schedule_factorization (&factoring);
  bool done = false;
#ifndef QUIET
  unsigned factored = 0;
#endif
  uint64_t *ticks = &solver->statistics.factor_ticks;
  kissat_extremely_verbose (
      solver, "factorization limit of %" PRIu64 " ticks", limit - *ticks);
  while (!done && !kissat_empty_heap (&factoring.schedule)) {
    const unsigned first =
        kissat_pop_max_heap (solver, &factoring.schedule);
    const unsigned first_idx = IDX (first);
    if (!ACTIVE (first_idx))
      continue;
    if (*ticks > limit) {
      kissat_very_verbose (solver, "factorization ticks limit hit");
      break;
    }
    if (TERMINATED (factor_terminated_1))
      break;
    struct flags *f = solver->flags + first_idx;
    const unsigned bit = 1u << NEGATED (first);
    if (!(f->factor & bit))
      continue;
    f->factor &= ~bit;
    const size_t first_count = first_factor (&factoring, first);
    if (first_count > 1) {
      for (;;) {
        unsigned next_count;
        const unsigned next = next_factor (&factoring, &next_count);
        if (next == INVALID_LIT)
          break;
        assert (next_count > 1);
        if (next_count < 2)
          break;
        factorize_next (&factoring, next, next_count);
      }
      size_t reduction;
      quotient *q = best_quotient (&factoring, &reduction);
      if (q && reduction > factoring.bound) {
        if (apply_factoring (&factoring, q)) {
#ifndef QUIET
          factored++;
#endif
        } else
          done = true;
      }
    }
    release_quotients (&factoring);
  }
  bool completed = kissat_empty_heap (&factoring.schedule);
  adjust_scores_and_phases_of_fresh_varaibles (&factoring);
  release_factoring (&factoring);
  REPORT (!factored, 'f');
  return completed;
}

// essentially do full occurence list as in elim.cpp
void Internal::factor_mode () {
  reset_watches ();

  assert (!watching ());
  init_occs ();

  const unsigned size_limit = opts.factorsize;

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
      occs[vlit (lit)].push_back (c);
      occs[vlit (other)].push_back (c);
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
    for (auto c = *q; c = *q++ = *p++; p != end) {
      for (const auto &lit : c) {
        const auto idx = vlit (lit);
        if (bincount[idx] + largecount[idx] < 2) {
          q--;
          goto CONTINUE_WITH_NEXT_CLAUSE;
        }
      }
      for (const auto &lit : c) {
        const auto idx = vlit (lit);
        newlargecount[idx]++;
      }
    CONTINUE_WITH_NEXT_CLAUSE:
    }
    candidates.resize (q - begin);
    largecount.swap (newlargecount);
  }

  for (const auto &c : candidates) {
    for (const auto &lit : *c) {
      const auto idx = vlit (lit);
      occs[idx].push_back (c);
    }
  }

}

// go back to two watch scheme
void Internal::reset_factor_mode () {
  reset_occs ();
  init_watches ();
  connect_watches ();
}

bool Internal::run_factorization (int64_t limit) {
  Factorizor factor = Factorizor ();
  factor_mode (factor);
  
  reset_factor_mode ();

  delete_all_factored (factor);
  report ('f', !factored);
  return false;
}

void Internal::factor () {
  if (unsat)
    return false;
  if (terminated_asynchronously ())
    return false;
  if (!opts.factor)
    return false;
  if (last.factor.marked >= stats.factor_literals) {
    VERBOSE (3, "factorization skipped as no literals have been
        "marked to be added (%" PRIu64 " < %" PRIu64 ")",
        last.factor.marked, stats.factor_literals);
    return;
  }
  assert (!level);
  START_SIMPLIFIER (factor, FACTOR);
  stats.factor++;

  uint64_t limit = opts.factoriniticks;
  if (stats.factor > 1) {
    int64_t tmp = stats.propagations - last.factor.ticks;
    tmp *= opts.factoreffort;
    limit = tmp;
  } else {
    VERBOSE (3, "initially limiting to %" PRIu64
               " million factorization ticks",
               limit);
    limit *= 1e6;
    limit += stats.factor_ticks;
  }

  // TODO

  struct {
    int64_t variables, clauses, ticks;
  } before, after, delta;
  before.variables = stats.variables_extension + stats.variables_original;
  before.ticks = stats.factor_ticks;

  kissat_enter_dense_mode (solver, 0);
  connect_clauses_to_factor (solver);
  bool completed = run_factorization (limit);
  kissat_resume_sparse_mode (solver, false, 0);
  updated_scores_for_new_variables (factored);
  
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
  if (completed)
    last.factor.marked = stats.factor_literals;
  STOP_SIMPLIFIER (factor, FACTOR);
}

}