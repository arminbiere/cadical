#include "citten.h"
#include "random.h"
#include "stack.h"

#include <assert.h>
#include <inttypes.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef signed char value;

void citten_error (const char *fmt, ...);

static inline void *citten_calloc (size_t n, size_t size) {
  void *res = calloc (n, size);
  if (n && size && !res)
    citten_error ("out of memory allocating '%zu * %zu' bytes", n, size);
  return res;
}

#define CALLOC(P, N) \
  do { \
    (P) = citten_calloc (N, sizeof *(P)); \
  } while (0)
#define DEALLOC(P, N) free (P)

#undef ENLARGE_STACK

// Use (S).begin as backup to old pointer to guarantee
// the memory can be freed in case of realloc failing.
// Store the new pointer temporarily in (S).allocated.
// Only if memory allocation succeeds overwrite (S).begin.
#define ENLARGE_STACK(S) \
  do { \
    assert (FULL_STACK (S)); \
    const size_t SIZE = SIZE_STACK (S); \
    const size_t OLD_CAPACITY = CAPACITY_STACK (S); \
    const size_t NEW_CAPACITY = OLD_CAPACITY ? 2 * OLD_CAPACITY : 1; \
    const size_t BYTES = NEW_CAPACITY * sizeof *(S).begin; \
    (S).allocated = realloc ((S).begin, BYTES); \
    if (!(S).allocated) \
      citten_error ("out of memory reallocating '%zu' bytes", BYTES); \
    (S).begin = (S).allocated; \
    (S).allocated = (S).begin + NEW_CAPACITY; \
    (S).end = (S).begin + SIZE; \
  } while (0)

// Beside allocators above also use stand alone statistics counters.

#define INC(NAME) \
  do { \
    statistics *statistics = &citten->statistics; \
    assert (statistics->NAME < UINT64_MAX); \
    statistics->NAME++; \
  } while (0)

#define ADD(NAME, DELTA) \
  do { \
    statistics *statistics = &citten->statistics; \
    assert (statistics->NAME <= UINT64_MAX - (DELTA)); \
    statistics->NAME += (DELTA); \
  } while (0)

#define CITTEN_TICKS (citten->statistics.citten_ticks)

#define INVALID UINT_MAX
#define MAX_VARS ((1u << 31) - 1)

#define CORE_FLAG (1u)
#define LEARNED_FLAG (2u)

// clang-format off

typedef struct kar kar;
typedef struct kink kink;
typedef struct klause klause;
typedef STACK (unsigned) klauses;
typedef unsigneds katches;

// clang-format on

struct kar {
  unsigned level;
  unsigned reason;
};

struct kink {
  unsigned next;
  unsigned prev;
  uint64_t stamp;
};

struct klause {
  unsigned aux;
  unsigned size;
  unsigned flags;
  unsigned lits[1];
};

typedef struct citten_statistics statistics;

typedef struct kimits kimits;

struct kimits {
  uint64_t ticks;
};

struct citten {
  // First zero initialized field in 'clear_citten' is 'status'.
  //
  int status;

#if defined(LOGGING)
  bool logging;
#endif
  bool antecedents;
  bool keep_assumptions;
  bool learned;

  unsigned level;
  unsigned propagated;
  unsigned unassigned;
  unsigned inconsistent;
  unsigned failing;

  uint64_t generator;

  size_t lits;
  size_t evars;

  size_t end_original_ref;
  unsigned last_klause_decision;

  struct {
    unsigned first, last;
    uint64_t stamp;
    unsigned search;
  } queue;

  // The 'size' field below is the first not zero reinitialized field
  // by 'memset' in 'clear_citten' (after 'kissat').

  size_t size;
  size_t esize;

  kar *vars;
  kink *links;
  value *marks;
  value *values;
  bool *failed;
  unsigned char *phases;
  unsigned *import;
  katches *watches;

  unsigneds analyzed;
  unsigneds assumptions;
  unsigneds core;
  unsigneds rcore;
  unsigneds eclause;
  unsigneds export;
  unsigneds klause;
  unsigneds klauses;
  unsigneds original_klause_refs; // of size > 1
  unsigneds klause_decision_control;
  unsigneds resolved;
  unsigneds trail;
  unsigneds units;
  unsigneds work;
  unsigneds prime;

  kimits limits;
  int (*terminator) (void *);
  void *terminator_data;
  unsigneds clause;
  uint64_t initialized;
  statistics statistics;
};

/*------------------------------------------------------------------------*/

static inline bool is_core_klause (klause *c) {
  return c->flags & CORE_FLAG;
}

static inline bool is_learned_klause (klause *c) {
  return c->flags & LEARNED_FLAG;
}

static inline void set_core_klause (klause *c) { c->flags |= CORE_FLAG; }

static inline void unset_core_klause (klause *c) { c->flags &= ~CORE_FLAG; }

static inline klause *dereference_klause (citten *citten, unsigned ref) {
  unsigned *res = BEGIN_STACK (citten->klauses) + ref;
  assert (res < END_STACK (citten->klauses));
  return (klause *) res;
}

static inline unsigned reference_klause (citten *citten, const klause *c) {
  const unsigned *const begin = BEGIN_STACK (citten->klauses);
  const unsigned *p = (const unsigned *) c;
  assert (begin <= p);
  assert (p < END_STACK (citten->klauses));
  const unsigned res = p - begin;
  return res;
}

/*------------------------------------------------------------------------*/

#define KATCHES(KIT) (citten->watches[assert ((KIT) < citten->lits), (KIT)])

#define all_klauses(C) \
  klause *C = begin_klauses (citten), *end_##C = end_klauses (citten); \
  (C) != end_##C; \
  (C) = next_klause (citten, C)

#define all_original_klauses(C) \
  klause *C = begin_klauses (citten), \
         *end_##C = end_original_klauses (citten); \
  (C) != end_##C; \
  (C) = next_klause (citten, C)

#define all_learned_klauses(C) \
  klause *C = begin_learned_klauses (citten), \
         *end_##C = end_klauses (citten); \
  (C) != end_##C; \
  (C) = next_klause (citten, C)

#define all_kits(KIT) \
  size_t KIT = 0, KIT_##END = citten->lits; \
  KIT != KIT_##END; \
  KIT++

#define BEGIN_KLAUSE(C) (C)->lits

#define END_KLAUSE(C) (BEGIN_KLAUSE (C) + (C)->size)

#define all_literals_in_klause(KIT, C) \
  unsigned KIT, *KIT##_PTR = BEGIN_KLAUSE (C), \
                *KIT##_END = END_KLAUSE (C); \
  KIT##_PTR != KIT##_END && ((KIT = *KIT##_PTR), true); \
  ++KIT##_PTR

#define all_antecedents(REF, C) \
  unsigned REF, *REF##_PTR = antecedents (C), \
                *REF##_END = REF##_PTR + (C)->aux; \
  REF##_PTR != REF##_END && ((REF = *REF##_PTR), true); \
  ++REF##_PTR

#ifdef LOGGING

#define logging (citten->logging)

static void log_basic (citten *, const char *, ...)
    __attribute__ ((format (printf, 2, 3)));

static void log_basic (citten *citten, const char *fmt, ...) {
  assert (logging);
  printf ("c CITTEN %u ", citten->level);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void log_reference (citten *, unsigned, const char *, ...)
    __attribute__ ((format (printf, 3, 4)));

static void log_reference (citten *citten, unsigned ref, const char *fmt,
                           ...) {
  klause *c = dereference_klause (citten, ref);
  assert (logging);
  printf ("c CITTEN %u ", citten->level);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  if (is_learned_klause (c)) {
    fputs (" learned", stdout);
    if (c->aux)
      printf ("[%u]", c->aux);
  } else {
    fputs (" original", stdout);
    if (c->aux)
      printf ("[%u]", c->aux);
  }
  printf (" size %u clause[%u]", c->size, ref);
  value *values = citten->values;
  kar *vars = citten->vars;
  for (all_literals_in_klause (lit, c)) {
    printf (" %u", lit);
    const value value = values[lit];
    if (value)
      printf ("@%u=%d", vars[lit / 2].level, (int) value);
  }
  fputc ('\n', stdout);
  fflush (stdout);
}

static void log_literals (citten *, unsigned *, unsigned, const char *, ...)
    __attribute__ ((format (printf, 4, 5)));

static void log_literals (citten *citten, unsigned *lits, unsigned size,
                          const char *fmt, ...) {
  assert (logging);
  printf ("c CITTEN %u ", citten->level);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  value *values = citten->values;
  kar *vars = citten->vars;
  for (unsigned i = 0; i < size; i++) {
    const unsigned lit = lits[i];
    printf (" %u", lit);
    const value value = values[lit];
    if (value)
      printf ("@%u=%d", vars[lit / 2].level, (int) value);
  }
  fputc ('\n', stdout);
  fflush (stdout);
}

#define LOG(...) \
  do { \
    if (logging) \
      log_basic (citten, __VA_ARGS__); \
  } while (0)

#define ROG(...) \
  do { \
    if (logging) \
      log_reference (citten, __VA_ARGS__); \
  } while (0)

#define LOGLITS(...) \
  do { \
    if (logging) \
      log_literals (citten, __VA_ARGS__); \
  } while (0)

#else

#define LOG(...) \
  do { \
  } while (0)
#define ROG(...) \
  do { \
  } while (0)
#define LOGLITS(...) \
  do { \
  } while (0)

#endif

static void check_queue (citten *citten) {
#ifdef CHECK_CITTEN
  const unsigned vars = citten->lits / 2;
  unsigned found = 0, prev = INVALID;
  kink *links = citten->links;
  uint64_t stamp = 0;
  for (unsigned idx = citten->queue.first, next; idx != INVALID;
       idx = next) {
    kink *link = links + idx;
    assert (link->prev == prev);
    assert (!found || stamp < link->stamp);
    assert (link->stamp < citten->queue.stamp);
    stamp = link->stamp;
    next = link->next;
    prev = idx;
    found++;
  }
  assert (found == vars);
  unsigned next = INVALID;
  found = 0;
  for (unsigned idx = citten->queue.last, prev; idx != INVALID;
       idx = prev) {
    kink *link = links + idx;
    assert (link->next == next);
    prev = link->prev;
    next = idx;
    found++;
  }
  assert (found == vars);
  value *values = citten->values;
  bool first = true;
  for (unsigned idx = citten->queue.search, next; idx != INVALID;
       idx = next) {
    kink *link = links + idx;
    next = link->next;
    const unsigned lit = 2 * idx;
    assert (first || values[lit]);
    first = false;
  }
#else
  (void) citten;
#endif
}

static void update_search (citten *citten, unsigned idx) {
  if (citten->queue.search == idx)
    return;
  citten->queue.search = idx;
  LOG ("search updated to %u stamped %" PRIu64, idx,
       citten->links[idx].stamp);
}

static void enqueue (citten *citten, unsigned idx) {
  LOG ("enqueue %u", idx);
  kink *links = citten->links;
  kink *l = links + idx;
  const unsigned last = citten->queue.last;
  if (last == INVALID)
    citten->queue.first = idx;
  else
    links[last].next = idx;
  l->prev = last;
  l->next = INVALID;
  citten->queue.last = idx;
  l->stamp = citten->queue.stamp++;
  LOG ("stamp %" PRIu64, l->stamp);
}

static void dequeue (citten *citten, unsigned idx) {
  LOG ("dequeue %u", idx);
  kink *links = citten->links;
  kink *l = links + idx;
  const unsigned prev = l->prev;
  const unsigned next = l->next;
  if (prev == INVALID)
    citten->queue.first = next;
  else
    links[prev].next = next;
  if (next == INVALID)
    citten->queue.last = prev;
  else
    links[next].prev = prev;
}

static void init_queue (citten *citten, size_t old_vars, size_t new_vars) {
  for (size_t idx = old_vars; idx < new_vars; idx++) {
    assert (!citten->values[2 * idx]);
    assert (citten->unassigned < UINT_MAX);
    citten->unassigned++;
    enqueue (citten, idx);
  }
  LOG ("initialized decision queue from %zu to %zu", old_vars, new_vars);
  update_search (citten, citten->queue.last);
  check_queue (citten);
}

static void initialize_citten (citten *citten) {
  citten->queue.first = INVALID;
  citten->queue.last = INVALID;
  citten->inconsistent = INVALID;
  citten->failing = INVALID;
  citten->queue.search = INVALID;
  citten->terminator = 0;
  citten->terminator_data = 0;
  citten->limits.ticks = UINT64_MAX;
  citten->generator = citten->initialized++;
}

static void clear_citten (citten *citten) {
  size_t bytes = (char *) &citten->size - (char *) &citten->status;
  memset (&citten->status, 0, bytes);
  memset (&citten->statistics, 0, sizeof (statistics));
  initialize_citten (citten);
}

#define RESIZE1(P) \
  do { \
    void *OLD_PTR = (P); \
    CALLOC ((P), new_size / 2); \
    const size_t BYTES = old_vars * sizeof *(P); \
    if ((P) && OLD_PTR) /* nullptr not allowed */ \
      memcpy ((P), OLD_PTR, BYTES); \
    void *NEW_PTR = (P); \
    (P) = OLD_PTR; \
    DEALLOC ((P), old_size / 2); \
    (P) = NEW_PTR; \
  } while (0)

#define RESIZE2(P) \
  do { \
    void *OLD_PTR = (P); \
    CALLOC ((P), new_size); \
    const size_t BYTES = old_lits * sizeof *(P); \
    if ((P) && OLD_PTR) /* nullptr not allowed */ \
      memcpy ((P), OLD_PTR, BYTES); \
    void *NEW_PTR = (P); \
    (P) = OLD_PTR; \
    DEALLOC ((P), old_size); \
    (P) = NEW_PTR; \
  } while (0)

static void enlarge_internal (citten *citten, size_t lit) {
  const size_t new_lits = (lit | 1) + 1;
  const size_t old_lits = citten->lits;
  assert (old_lits <= lit);
  assert (old_lits < new_lits);
  assert ((lit ^ 1) < new_lits);
  assert (lit < new_lits);
  const size_t old_size = citten->size;
  const unsigned new_vars = new_lits / 2;
  const unsigned old_vars = old_lits / 2;
  if (old_size < new_lits) {
    size_t new_size = old_size ? 2 * old_size : 2;
    while (new_size <= lit)
      new_size *= 2;
    LOG ("internal literals resized to %zu from %zu (requested %zu)",
         new_size, old_size, new_lits);

    RESIZE1 (citten->marks);
    RESIZE1 (citten->phases);
    RESIZE2 (citten->values);
    RESIZE2 (citten->failed);
    RESIZE1 (citten->vars);
    RESIZE1 (citten->links);
    RESIZE2 (citten->watches);

    citten->size = new_size;
  }
  citten->lits = new_lits;
  init_queue (citten, old_vars, new_vars);
  LOG ("internal literals activated until %zu literals", new_lits);
  return;
}

static const char *status_to_string (int status) {
  switch (status) {
  case 10:
    return "formula satisfied";
  case 11:
    return "formula satisfied and prime implicant computed";
  case 20:
    return "formula inconsistent";
  case 21:
    return "formula inconsistent and core computed";
  default:
    assert (!status);
    return "formula unsolved";
  }
}

static void invalid_api_usage (const char *fun, const char *fmt, ...) {
  fprintf (stderr, "citten: fatal error: invalid API usage in '%s': ", fun);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  abort ();
}

#define INVALID_API_USAGE(...) invalid_api_usage (__func__, __VA_ARGS__)

#define REQUIRE_INITIALIZED() \
  do { \
    if (!citten) \
      INVALID_API_USAGE ("solver argument zero"); \
  } while (0)

#define REQUIRE_FALSIFIED_STATUS() \
  do { \
    REQUIRE_INITIALIZED (); \
    if (!(citten->status == 20 || citten->status == 21)) \
      INVALID_API_USAGE ("invalid status '%s' (expected '%s' or '%s')", \
                         status_to_string (citten->status), \
                         status_to_string (20), status_to_string (21)); \
  } while (0)

#define REQUIRE_SATISFIED_STATUS() \
  do { \
    REQUIRE_INITIALIZED (); \
    if (!(citten->status == 10 || citten->status == 11)) \
      INVALID_API_USAGE ("invalid status '%s' (expected '%s' or '%s')", \
                         status_to_string (citten->status), \
                         status_to_string (10), status_to_string (11)); \
  } while (0)

#define REQUIRE_STATUS(EXPECTED) \
  do { \
    REQUIRE_INITIALIZED (); \
    if (citten->status != (EXPECTED)) \
      INVALID_API_USAGE ("invalid status '%s' (expected '%s')", \
                         status_to_string (citten->status), \
                         status_to_string (EXPECTED)); \
  } while (0)

#define UPDATE_STATUS(STATUS) \
  do { \
    if (citten->status != (STATUS)) \
      LOG ("updating status from '%s' to '%s'", \
           status_to_string (citten->status), status_to_string (STATUS)); \
    else \
      LOG ("keeping status at '%s'", status_to_string (STATUS)); \
    citten->status = (STATUS); \
  } while (0)

citten *citten_init (void) {
  citten *citten;
  CALLOC (citten, 1);
  initialize_citten (citten);
  return citten;
}

statistics *citten_get_statistics (citten *citten) {
  if (!citten)
    return 0;
  return &citten->statistics;
}

#ifdef LOGGING
void citten_set_logging (citten *citten) { logging = true; }
#endif

void citten_track_antecedents (citten *citten) {
  REQUIRE_STATUS (0);

  if (citten->learned)
    INVALID_API_USAGE ("can not start tracking antecedents after learning");

  LOG ("enabling antecedents tracking");
  citten->antecedents = true;
}

void citten_keep_assumptions (citten *citten) {
  REQUIRE_STATUS (0);

  LOG ("not resetting assumptions after solve");
  citten->keep_assumptions = true;
}

void citten_randomize_phases (citten *citten) {
  REQUIRE_INITIALIZED ();

  LOG ("randomizing phases");

  unsigned char *phases = citten->phases;
  const unsigned vars = citten->size / 2;

  uint64_t random = kissat_next_random64 (&citten->generator);

  unsigned i = 0;
  const unsigned rest = vars & ~63u;

  while (i != rest) {
    uint64_t *p = (uint64_t *) (phases + i);
    p[0] = (random >> 0) & 0x0101010101010101;
    p[1] = (random >> 1) & 0x0101010101010101;
    p[2] = (random >> 2) & 0x0101010101010101;
    p[3] = (random >> 3) & 0x0101010101010101;
    p[4] = (random >> 4) & 0x0101010101010101;
    p[5] = (random >> 5) & 0x0101010101010101;
    p[6] = (random >> 6) & 0x0101010101010101;
    p[7] = (random >> 7) & 0x0101010101010101;
    random = kissat_next_random64 (&citten->generator);
    i += 64;
  }

  unsigned shift = 0;
  while (i != vars)
    phases[i++] = (random >> shift++) & 1;
}

void citten_flip_phases (citten *citten) {
  REQUIRE_INITIALIZED ();

  LOG ("flipping phases");

  unsigned char *phases = citten->phases;
  const unsigned vars = citten->size / 2;

  unsigned i = 0;
  const unsigned rest = vars & ~7u;

  while (i != rest) {
    uint64_t *p = (uint64_t *) (phases + i);
    *p ^= 0x0101010101010101;
    i += 8;
  }

  while (i != vars)
    phases[i++] ^= 1;
}

void citten_no_ticks_limit (citten *citten) {
  REQUIRE_INITIALIZED ();
  LOG ("forcing no ticks limit");
  citten->limits.ticks = UINT64_MAX;
}

uint64_t citten_current_ticks (citten *citten) {
  REQUIRE_INITIALIZED ();
  const uint64_t current = CITTEN_TICKS;
  return current;
}

void citten_set_ticks_limit (citten *citten, uint64_t delta) {
  REQUIRE_INITIALIZED ();
  const uint64_t current = CITTEN_TICKS;
  uint64_t limit;
  if (UINT64_MAX - delta <= current) {
    LOG ("forcing unlimited ticks limit");
    limit = UINT64_MAX;
  } else {
    limit = current + delta;
    LOG ("new limit of %" PRIu64 " ticks after %" PRIu64, limit, delta);
  }

  citten->limits.ticks = limit;
}

void citten_no_terminator (citten *citten) {
  REQUIRE_INITIALIZED ();
  LOG ("removing terminator");
  citten->terminator = 0;
  citten->terminator_data = 0;
}

void citten_set_terminator (citten *citten, void *data,
                            int (*terminator) (void *)) {
  REQUIRE_INITIALIZED ();
  LOG ("setting terminator");
  citten->terminator = terminator;
  citten->terminator_data = data;
}

static void shuffle_unsigned_array (citten *citten, size_t size,
                                    unsigned *a) {
  for (size_t i = 0; i < size; i++) {
    const size_t j = kissat_pick_random (&citten->generator, 0, i);
    if (j == i)
      continue;
    const unsigned first = a[i];
    const unsigned second = a[j];
    a[i] = second;
    a[j] = first;
  }
}

static void shuffle_unsigned_stack (citten *citten, unsigneds *stack) {
  const size_t size = SIZE_STACK (*stack);
  unsigned *a = BEGIN_STACK (*stack);
  shuffle_unsigned_array (citten, size, a);
}

static void shuffle_katches (citten *citten) {
  LOG ("shuffling watch lists");
  for (size_t lit = 0; lit < citten->lits; lit++)
    shuffle_unsigned_stack (citten, &KATCHES (lit));
}

static void shuffle_queue (citten *citten) {
  LOG ("shuffling variable decision order");

  const unsigned vars = citten->lits / 2;
  for (unsigned i = 0; i < vars; i++) {
    const unsigned idx = kissat_pick_random (&citten->generator, 0, vars);
    dequeue (citten, idx);
    enqueue (citten, idx);
  }
  update_search (citten, citten->queue.last);
}

static void shuffle_units (citten *citten) {
  LOG ("shuffling units");
  shuffle_unsigned_stack (citten, &citten->units);
}

void citten_shuffle_clauses (citten *citten) {
  REQUIRE_STATUS (0);
  shuffle_queue (citten);
  shuffle_katches (citten);
  shuffle_units (citten);
}

static inline unsigned *antecedents (klause *c) {
  assert (is_learned_klause (c));
  return c->lits + c->size;
}

static inline void watch_klause (citten *citten, unsigned lit,
                                 unsigned ref) {
  ROG (ref, "watching %u in", lit);
  katches *watches = &KATCHES (lit);
  PUSH_STACK (*watches, ref);
}

static inline void connect_new_klause (citten *citten, unsigned ref) {
  ROG (ref, "new");

  klause *c = dereference_klause (citten, ref);

  if (!c->size) {
    if (citten->inconsistent == INVALID) {
      ROG (ref, "registering inconsistent empty");
      citten->inconsistent = ref;
    } else
      ROG (ref, "ignoring inconsistent empty");
  } else if (c->size == 1) {
    ROG (ref, "watching unit");
    PUSH_STACK (citten->units, ref);
  } else {
    watch_klause (citten, c->lits[0], ref);
    watch_klause (citten, c->lits[1], ref);
  }
}

static unsigned new_reference (citten *citten) {
  size_t ref = SIZE_STACK (citten->klauses);
  if (ref >= INVALID) {
    citten_error ("maximum number of literals exhausted");
  }
  const unsigned res = (unsigned) ref;
  assert (res != INVALID);
  INC (citten_ticks);
  return res;
}

static void new_original_klause (citten *citten, unsigned id) {
  unsigned res = new_reference (citten);
  unsigned size = SIZE_STACK (citten->klause);
  unsigneds *klauses = &citten->klauses;
  unsigneds *original_klause_refs = &citten->original_klause_refs;
  if (size > 1)
    PUSH_STACK (*original_klause_refs, SIZE_STACK (*klauses));
  PUSH_STACK (*klauses, id);
  PUSH_STACK (*klauses, size);
  PUSH_STACK (*klauses, 0);
  for (all_stack (unsigned, lit, citten->klause))
    PUSH_STACK (*klauses, lit);
  connect_new_klause (citten, res);
  citten->end_original_ref = SIZE_STACK (*klauses);
  citten->last_klause_decision = SIZE_STACK (*original_klause_refs);
  INC (original);
}

static void enlarge_external (citten *citten, size_t eidx) {
  const size_t old_size = citten->esize;
  const unsigned old_evars = citten->evars;
  assert (old_evars <= eidx);
  const unsigned new_evars = eidx + 1;
  if (old_size <= eidx) {
    size_t new_size = old_size ? 2 * old_size : 1;
    while (new_size <= eidx)
      new_size *= 2;
    LOG ("external resizing to %zu variables from %zu (requested %u)",
         new_size, old_size, new_evars);
    unsigned *old_import = citten->import;
    CALLOC (citten->import, new_size);
    const size_t bytes = old_evars * sizeof *citten->import;
    if (citten->import && old_import)
      memcpy (citten->import, old_import, bytes);
    DEALLOC (old_import, old_size);
    citten->esize = new_size;
  }
  citten->evars = new_evars;
  LOG ("external variables enlarged to %u", new_evars);
}

static unsigned import_literal (citten *citten, unsigned elit) {
  const unsigned eidx = elit / 2;
  if (eidx >= citten->evars)
    enlarge_external (citten, eidx);

  unsigned iidx = citten->import[eidx];
  if (!iidx) {
    iidx = SIZE_STACK (citten->export);
    PUSH_STACK (citten->export, eidx);
    citten->import[eidx] = iidx + 1;
  } else
    iidx--;
  unsigned ilit = 2 * iidx + (elit & 1);
  LOG ("imported external literal %u as internal literal %u", elit, ilit);
  if (ilit >= citten->lits)
    enlarge_internal (citten, ilit);
  return ilit;
}

static unsigned export_literal (citten *citten, unsigned ilit) {
  const unsigned iidx = ilit / 2;
  assert (iidx < SIZE_STACK (citten->export));
  const unsigned eidx = PEEK_STACK (citten->export, iidx);
  const unsigned elit = 2 * eidx + (ilit & 1);
  return elit;
}

unsigned new_learned_klause (citten *citten) {
  unsigned res = new_reference (citten);
  unsigneds *klauses = &citten->klauses;
  const size_t size = SIZE_STACK (citten->klause);
  assert (size <= UINT_MAX);
  const size_t aux =
      citten->antecedents ? SIZE_STACK (citten->resolved) : 0;
  assert (aux <= UINT_MAX);
  PUSH_STACK (*klauses, (unsigned) aux);
  PUSH_STACK (*klauses, (unsigned) size);
  PUSH_STACK (*klauses, LEARNED_FLAG);
  for (all_stack (unsigned, lit, citten->klause))
    PUSH_STACK (*klauses, lit);
  if (aux)
    for (all_stack (unsigned, ref, citten->resolved))
      PUSH_STACK (*klauses, ref);
  connect_new_klause (citten, res);
  citten->learned = true;
  INC (learned);
  return res;
}

void citten_clear (citten *citten) {
  LOG ("clear citten of size %zu", citten->size);

  assert (EMPTY_STACK (citten->analyzed));
  assert (EMPTY_STACK (citten->eclause));
  assert (EMPTY_STACK (citten->resolved));

  CLEAR_STACK (citten->assumptions);
  CLEAR_STACK (citten->core);
  CLEAR_STACK (citten->klause);
  CLEAR_STACK (citten->klauses);
  CLEAR_STACK (citten->trail);
  CLEAR_STACK (citten->units);
  CLEAR_STACK (citten->clause);
  CLEAR_STACK (citten->prime);

  for (all_kits (kit))
    CLEAR_STACK (KATCHES (kit));

  while (!EMPTY_STACK (citten->export))
    citten->import[POP_STACK (citten->export)] = 0;

  const size_t lits = citten->size;
  const unsigned vars = lits / 2;

#ifndef NDEBUG
  for (unsigned i = 0; i < vars; i++)
    assert (!citten->marks[i]);
#endif

  if (citten->phases)
    memset (citten->phases, 0, vars);
  if (citten->values)
    memset (citten->values, 0, lits);
  if (citten->failed)
    memset (citten->failed, 0, lits);
  if (citten->vars)
    memset (citten->vars, 0, vars);

  clear_citten (citten);
}

void citten_release (citten *citten) {
  RELEASE_STACK (citten->analyzed);
  RELEASE_STACK (citten->assumptions);
  RELEASE_STACK (citten->core);
  RELEASE_STACK (citten->eclause);
  RELEASE_STACK (citten->export);
  RELEASE_STACK (citten->klause);
  RELEASE_STACK (citten->klauses);
  RELEASE_STACK (citten->original_klause_refs);
  RELEASE_STACK (citten->klause_decision_control);
  RELEASE_STACK (citten->resolved);
  RELEASE_STACK (citten->trail);
  RELEASE_STACK (citten->units);
  RELEASE_STACK (citten->clause);
  RELEASE_STACK (citten->work);
  RELEASE_STACK (citten->prime);

  for (size_t lit = 0; lit < citten->size; lit++)
    RELEASE_STACK (citten->watches[lit]);

  const size_t lits = citten->size;
  const unsigned vars = lits / 2;
  DEALLOC (citten->marks, vars);
  DEALLOC (citten->phases, vars);
  DEALLOC (citten->values, lits);
  DEALLOC (citten->failed, lits);
  DEALLOC (citten->vars, vars);
  DEALLOC (citten->links, vars);
  DEALLOC (citten->watches, lits);
  DEALLOC (citten->import, citten->esize);
  (void) vars;

  free (citten);
}

static inline void move_to_front (citten *citten, unsigned idx) {
  if (idx == citten->queue.last)
    return;
  LOG ("move to front variable %u", idx);
  dequeue (citten, idx);
  enqueue (citten, idx);
  assert (citten->values[2 * idx]);
}

static inline void assign (citten *citten, unsigned lit, unsigned reason) {
#ifdef LOGGING
  if (reason == INVALID)
    LOG ("assign %u as decision", lit);
  else
    ROG (reason, "assign %u reason", lit);
#endif
  value *values = citten->values;
  const unsigned not_lit = lit ^ 1;
  assert (!values[lit]);
  assert (!values[not_lit]);
  values[lit] = 1;
  values[not_lit] = -1;
  const unsigned idx = lit / 2;
  const unsigned sign = lit & 1;
  citten->phases[idx] = sign;
  PUSH_STACK (citten->trail, lit);
  kar *v = citten->vars + idx;
  v->level = citten->level;
  if (!v->level) {
    assert (reason != INVALID);
    klause *c = dereference_klause (citten, reason);
    if (c->size > 1) {
      if (citten->antecedents) {
        PUSH_STACK (citten->resolved, reason);
        for (all_literals_in_klause (other, c))
          if (other != lit) {
            const unsigned other_idx = other / 2;
            const unsigned other_ref = citten->vars[other_idx].reason;
            assert (other_ref != INVALID);
            PUSH_STACK (citten->resolved, other_ref);
          }
      }
      PUSH_STACK (citten->klause, lit);
      reason = new_learned_klause (citten);
      CLEAR_STACK (citten->resolved);
      CLEAR_STACK (citten->klause);
    }
  }
  v->reason = reason;
  assert (citten->unassigned);
  citten->unassigned--;
}

static inline unsigned propagate_literal (citten *citten, unsigned lit) {
  LOG ("propagating %u", lit);
  value *values = citten->values;
  assert (values[lit] > 0);
  const unsigned not_lit = lit ^ 1;
  katches *watches = citten->watches + not_lit;
  unsigned conflict = INVALID;
  unsigned *q = BEGIN_STACK (*watches);
  const unsigned *const end_watches = END_STACK (*watches);
  unsigned const *p = q;
  uint64_t ticks =
      (((const char *const) end_watches - (char *const) q) >> 7) + 1;
  while (p != end_watches) {
    const unsigned ref = *q++ = *p++;
    klause *c = dereference_klause (citten, ref);
    assert (c->size > 1);
    unsigned *lits = c->lits;
    const unsigned other = lits[0] ^ lits[1] ^ not_lit;
    const value other_value = values[other];
    ticks++;
    if (other_value > 0)
      continue;
    value replacement_value = -1;
    unsigned replacement = INVALID;
    const unsigned *const end_lits = lits + c->size;
    unsigned *r;
    for (r = lits + 2; r != end_lits; r++) {
      replacement = *r;
      replacement_value = values[replacement];
      if (replacement_value >= 0)
        break;
    }
    if (replacement_value >= 0) {
      assert (replacement != INVALID);
      ROG (ref, "unwatching %u in", not_lit);
      lits[0] = other;
      lits[1] = replacement;
      *r = not_lit;
      watch_klause (citten, replacement, ref);
      q--;
    } else if (other_value < 0) {
      ROG (ref, "conflict");
      INC (citten_conflicts);
      conflict = ref;
      break;
    } else {
      assert (!other_value);
      assign (citten, other, ref);
    }
  }
  while (p != end_watches)
    *q++ = *p++;
  SET_END_OF_STACK (*watches, q);
  ADD (citten_ticks, ticks);
  return conflict;
}

static inline unsigned propagate (citten *citten) {
  assert (citten->inconsistent == INVALID);
  unsigned propagated = 0;
  unsigned conflict = INVALID;
  while (conflict == INVALID &&
         citten->propagated < SIZE_STACK (citten->trail)) {
    if (citten->terminator &&
        citten->terminator (citten->terminator_data)) {
      break;
    }
    const unsigned lit = PEEK_STACK (citten->trail, citten->propagated);
    conflict = propagate_literal (citten, lit);
    citten->propagated++;
    propagated++;
  }
  ADD (citten_propagations, propagated);
  return conflict;
}

static void bump (citten *citten) {
  value *marks = citten->marks;
  for (all_stack (unsigned, idx, citten->analyzed)) {
    marks[idx] = 0;
    move_to_front (citten, idx);
  }
  check_queue (citten);
}

static inline void unassign (citten *citten, value *values, unsigned lit) {
  const unsigned not_lit = lit ^ 1;
  assert (citten->status == 11 || values[lit]);
  assert (citten->status == 11 || values[not_lit]);
  const unsigned idx = lit / 2;
#ifdef LOGGING
  kar *var = citten->vars + idx;
  citten->level = var->level;
  LOG ("unassign %u", lit);
#endif
  values[lit] = values[not_lit] = 0;
  assert (citten->unassigned < citten->lits / 2);
  citten->unassigned++;
  kink *links = citten->links;
  kink *link = links + idx;
  if (link->stamp > links[citten->queue.search].stamp)
    update_search (citten, idx);
}

static void backtrack (citten *citten, unsigned jump) {
  check_queue (citten);
  assert (jump < citten->level);
  LOG ("back%s to level %u",
       (citten->level == jump + 1 ? "tracking" : "jumping"), jump);
  kar *vars = citten->vars;
  value *values = citten->values;
  unsigneds *trail = &citten->trail;
  while (!EMPTY_STACK (*trail)) {
    const unsigned lit = TOP_STACK (*trail);
    const unsigned idx = lit / 2;
    const unsigned level = vars[idx].level;
    if (level == jump)
      break;
    (void) POP_STACK (*trail);
    unassign (citten, values, lit);
  }
  citten->propagated = SIZE_STACK (*trail);
  citten->level = jump;
  check_queue (citten);
}

void completely_backtrack_to_root_level (citten *citten) {
  check_queue (citten);
  LOG ("completely backtracking to level 0");
  value *values = citten->values;
  unsigneds *trail = &citten->trail;
  unsigneds *units = &citten->units;
#ifndef NDEBUG
  kar *vars = citten->vars;
#endif
  for (all_stack (unsigned, lit, *trail)) {
    assert (vars[lit / 2].level);
    unassign (citten, values, lit);
  }
  CLEAR_STACK (*trail);
  for (all_stack (unsigned, ref, *units)) {
    klause *c = dereference_klause (citten, ref);
    assert (c->size == 1);
    const unsigned unit = c->lits[0];
    const value value = values[unit];
    if (value <= 0)
      continue;
    unassign (citten, values, unit);
  }
  citten->propagated = 0;
  citten->level = 0;
  check_queue (citten);
}

static void analyze (citten *citten, unsigned conflict) {
  assert (citten->level);
  assert (citten->inconsistent == INVALID);
  assert (EMPTY_STACK (citten->analyzed));
  assert (EMPTY_STACK (citten->resolved));
  assert (EMPTY_STACK (citten->klause));
  PUSH_STACK (citten->klause, INVALID);
  unsigned reason = conflict;
  value *marks = citten->marks;
  const kar *const vars = citten->vars;
  const unsigned level = citten->level;
  unsigned const *p = END_STACK (citten->trail);
  unsigned open = 0, jump = 0, size = 1, uip;
  for (;;) {
    assert (reason != INVALID);
    klause *c = dereference_klause (citten, reason);
    assert (c);
    ROG (reason, "analyzing");
    PUSH_STACK (citten->resolved, reason);
    for (all_literals_in_klause (lit, c)) {
      const unsigned idx = lit / 2;
      if (marks[idx])
        continue;
      assert (citten->values[lit] < 0);
      LOG ("analyzed %u", lit);
      marks[idx] = true;
      PUSH_STACK (citten->analyzed, idx);
      const kar *const v = vars + idx;
      const unsigned tmp = v->level;
      if (tmp < level) {
        if (tmp > jump) {
          jump = tmp;
          if (size > 1) {
            const unsigned other = PEEK_STACK (citten->klause, 1);
            POKE_STACK (citten->klause, 1, lit);
            lit = other;
          }
        }
        PUSH_STACK (citten->klause, lit);
        size++;
      } else
        open++;
    }
    unsigned idx;
    do {
      assert (BEGIN_STACK (citten->trail) < p);
      uip = *--p;
    } while (!marks[idx = uip / 2]);
    assert (open);
    if (!--open)
      break;
    reason = vars[idx].reason;
  }
  const unsigned not_uip = uip ^ 1;
  LOG ("first UIP %u jump level %u size %u", not_uip, jump, size);
  POKE_STACK (citten->klause, 0, not_uip);
  bump (citten);
  CLEAR_STACK (citten->analyzed);
  const unsigned learned_ref = new_learned_klause (citten);
  CLEAR_STACK (citten->resolved);
  CLEAR_STACK (citten->klause);
  backtrack (citten, jump);
  assign (citten, not_uip, learned_ref);
}

static void failing (citten *citten) {
  assert (citten->inconsistent == INVALID);
  assert (!EMPTY_STACK (citten->assumptions));
  assert (EMPTY_STACK (citten->analyzed));
  assert (EMPTY_STACK (citten->resolved));
  assert (EMPTY_STACK (citten->klause));
  LOG ("analyzing failing assumptions");
  const value *const values = citten->values;
  const kar *const vars = citten->vars;
  unsigned failed_clashing = INVALID;
  unsigned first_failed = INVALID;
  unsigned failed_unit = INVALID;
  for (all_stack (unsigned, lit, citten->assumptions)) {
    if (values[lit] >= 0)
      continue;
    if (first_failed == INVALID)
      first_failed = lit;
    const unsigned failed_idx = lit / 2;
    const kar *const failed_var = vars + failed_idx;
    if (!failed_var->level) {
      failed_unit = lit;
      break;
    }
    if (failed_clashing == INVALID && failed_var->reason == INVALID)
      failed_clashing = lit;
  }
  unsigned failed;
  if (failed_unit != INVALID)
    failed = failed_unit;
  else if (failed_clashing != INVALID)
    failed = failed_clashing;
  else
    failed = first_failed;
  assert (failed != INVALID);
  const unsigned failed_idx = failed / 2;
  const kar *const failed_var = vars + failed_idx;
  const unsigned failed_reason = failed_var->reason;
  LOG ("first failed assumption %u", failed);
  citten->failed[failed] = true;

  if (failed_unit != INVALID) {
    assert (dereference_klause (citten, failed_reason)->size == 1);
    LOG ("root-level falsified assumption %u", failed);
    citten->failing = failed_reason;
    ROG (citten->failing, "failing reason");
    return;
  }

  const unsigned not_failed = failed ^ 1;
  if (failed_clashing != INVALID) {
    LOG ("clashing with negated assumption %u", not_failed);
    citten->failed[not_failed] = true;
    assert (citten->failing == INVALID);
    return;
  }

  value *marks = citten->marks;
  assert (!marks[failed_idx]);
  marks[failed_idx] = true;
  PUSH_STACK (citten->analyzed, failed_idx);
  PUSH_STACK (citten->klause, not_failed);

  LOGLITS (BEGIN_STACK (citten->trail), SIZE_STACK (citten->trail),
           "trail");

  assert (SIZE_STACK (citten->trail));
  unsigned const *p = END_STACK (citten->trail);
  unsigned open = 1;
  for (;;) {
    if (!open)
      break;
    open--;
    unsigned idx, uip;
    do {
      assert (BEGIN_STACK (citten->trail) < p);
      uip = *--p;
    } while (!marks[idx = uip / 2]);

    const kar *var = vars + idx;
    const unsigned reason = var->reason;
    if (reason == INVALID) {
      unsigned lit = 2 * idx;
      if (values[lit] < 0)
        lit ^= 1;
      LOG ("failed assumption %u", lit);
      assert (!citten->failed[lit]);
      citten->failed[lit] = true;
      const unsigned not_lit = lit ^ 1;
      PUSH_STACK (citten->klause, not_lit);
    } else {
      ROG (reason, "analyzing");
      PUSH_STACK (citten->resolved, reason);
      klause *c = dereference_klause (citten, reason);
      for (all_literals_in_klause (other, c)) {
        const unsigned other_idx = other / 2;
        if (marks[other_idx])
          continue;
        assert (other_idx != idx);
        marks[other_idx] = true;
        assert (values[other]);
        if (vars[other_idx].level)
          open++;
        else
          PUSH_STACK (citten->work, other_idx);
        PUSH_STACK (citten->analyzed, other_idx);

        LOG ("analyzing final literal %u", other ^ 1);
      }
    }
  }
  for (size_t next = 0; next < SIZE_STACK (citten->work); next++) {
    const unsigned idx = PEEK_STACK (citten->work, next);
    const kar *var = vars + idx;
    const unsigned reason = var->reason;
    if (reason == INVALID) {
      unsigned lit = 2 * idx;
      if (values[lit] < 0)
        lit ^= 1;
      LOG ("failed assumption %u", lit);
      assert (!citten->failed[lit]);
      citten->failed[lit] = true;
      const unsigned not_lit = lit ^ 1;
      PUSH_STACK (citten->klause, not_lit);
    } else {
      ROG (reason, "analyzing unit");
      PUSH_STACK (citten->resolved, reason);
    }
  }

  for (all_stack (unsigned, idx, citten->analyzed))
    assert (marks[idx]), marks[idx] = 0;
  CLEAR_STACK (citten->analyzed);

  const size_t resolved = SIZE_STACK (citten->resolved);
  assert (resolved);

  if (resolved == 1) {
    citten->failing = PEEK_STACK (citten->resolved, 0);
    ROG (citten->failing, "reusing as core");
  } else {
    citten->failing = new_learned_klause (citten);
    ROG (citten->failing, "new core");
  }

  CLEAR_STACK (citten->work);
  CLEAR_STACK (citten->resolved);
  CLEAR_STACK (citten->klause);
}

static void flush_trail (citten *citten) {
  unsigneds *trail = &citten->trail;
  LOG ("flushing %zu root-level literals from trail", SIZE_STACK (*trail));
  assert (!citten->level);
  citten->propagated = 0;
  CLEAR_STACK (*trail);
}

static int decide (citten *citten) {
  if (!citten->level && !EMPTY_STACK (citten->trail))
    flush_trail (citten);

  const value *const values = citten->values;
  unsigned decision = INVALID;
  const size_t assumptions = SIZE_STACK (citten->assumptions);
  while (citten->level < assumptions) {
    unsigned assumption = PEEK_STACK (citten->assumptions, citten->level);
    value value = values[assumption];
    if (value < 0) {
      LOG ("found failing assumption %u", assumption);
      failing (citten);
      return 20;
    } else if (value > 0) {

      citten->level++;
      LOG ("pseudo decision level %u for already satisfied assumption %u",
           citten->level, assumption);
    } else {
      decision = assumption;
      LOG ("using assumption %u as decision", decision);
      break;
    }
  }

  if (!citten->unassigned)
    return 10;

  if (CITTEN_TICKS >= citten->limits.ticks) {
    LOG ("ticks limit %" PRIu64 " hit after %" PRIu64 " ticks",
         citten->limits.ticks, CITTEN_TICKS);
    return -1;
  }

  if (citten->terminator && citten->terminator (citten->terminator_data)) {
    LOG ("terminator requested termination");
    return -1;
  }

  if (decision == INVALID) {
    unsigned idx = citten->queue.search;
    const kink *const links = citten->links;
    for (;;) {
      assert (idx != INVALID);
      if (!values[2 * idx])
        break;
      idx = links[idx].prev;
    }
    update_search (citten, idx);
    const unsigned phase = citten->phases[idx];
    decision = 2 * idx + phase;
    LOG ("decision %u variable %u phase %u", decision, idx, phase);
  }
  INC (citten_decisions);
  citten->level++;
  assign (citten, decision, INVALID);
  return 0;
}

static int decide_next_clause (citten *citten) {
  if (!citten->level && !EMPTY_STACK (citten->trail))
    flush_trail (citten);
  unsigneds *klause_decision_control = &citten->klause_decision_control;
  unsigned *last_klause_decision = &citten->last_klause_decision;
  while (citten->level < SIZE_STACK (*klause_decision_control)) {
    *last_klause_decision = POP_STACK (*klause_decision_control);
  }

  const value *const values = citten->values;
  unsigned decision = INVALID;
  const size_t assumptions = SIZE_STACK (citten->assumptions);
  while (citten->level < assumptions) {
    unsigned assumption = PEEK_STACK (citten->assumptions, citten->level);
    value value = values[assumption];
    if (value < 0) {
      LOG ("found failing assumption %u", assumption);
      failing (citten);
      return 20;
    } else if (value > 0) {

      citten->level++;
      PUSH_STACK (*klause_decision_control, *last_klause_decision);
      LOG ("pseudo decision level %u for already satisfied assumption %u",
           citten->level, assumption);
    } else {
      decision = assumption;
      LOG ("using assumption %u as decision", decision);
      break;
    }
  }

  if (!citten->unassigned)
    return 10;

  if (CITTEN_TICKS >= citten->limits.ticks) {
    LOG ("ticks limit %" PRIu64 " hit after %" PRIu64 " ticks",
         citten->limits.ticks, CITTEN_TICKS);
    return -1;
  }

  if (citten->terminator && citten->terminator (citten->terminator_data)) {
    LOG ("terminator requested termination");
    return -1;
  }

  if (decision != INVALID) {
    INC (citten_decisions);
    citten->level++;
    PUSH_STACK (*klause_decision_control, *last_klause_decision);
    assign (citten, decision, INVALID);
    return 0;
  }

  kink *const links = citten->links;
  const unsigned *const okr_begin =
      BEGIN_STACK (citten->original_klause_refs);
  while (*last_klause_decision) {
    const unsigned kref = *(okr_begin + *--last_klause_decision);
    klause *c = dereference_klause (citten, kref);
    assert (c->size >= 1);
    assert (!is_learned_klause (c));
    unsigned best = c->lits[0];
    uint64_t best_stamp = (links + (best / 2))->stamp;
    for (all_literals_in_klause (lit, c)) {
      const value v = values[lit];
      if (v > 0) {
        best = INVALID; // skip satisfied clause
        break;
      } else if (v < 0)
        continue;
      const unsigned lit_idx = lit / 2;
      kink *const l = links + lit_idx;
      const uint64_t stamp = l->stamp;
      if (stamp <= best_stamp)
        continue;
      best = lit;
      best_stamp = stamp;
    }
    decision = best;
  }
  if (decision == INVALID)
    return 11;
  INC (citten_decisions);
  PUSH_STACK (*klause_decision_control, *last_klause_decision);
  citten->level++;
  assign (citten, decision, INVALID);
  return 0;
}

static void inconsistent (citten *citten, unsigned ref) {
  assert (ref != INVALID);
  assert (citten->inconsistent == INVALID);

  if (!citten->antecedents) {
    citten->inconsistent = ref;
    ROG (ref, "registering inconsistent virtually empty");
    return;
  }

  unsigneds *analyzed = &citten->analyzed;
  unsigneds *resolved = &citten->resolved;

  assert (EMPTY_STACK (*analyzed));
  assert (EMPTY_STACK (*resolved));

  value *marks = citten->marks;
  const kar *const vars = citten->vars;
  unsigned next = 0;

  for (;;) {
    assert (ref != INVALID);
    klause *c = dereference_klause (citten, ref);
    assert (c);
    ROG (ref, "analyzing inconsistent");
    PUSH_STACK (*resolved, ref);
    for (all_literals_in_klause (lit, c)) {
      const unsigned idx = lit / 2;
      assert (!vars[idx].level);
      if (marks[idx])
        continue;
      assert (citten->values[lit] < 0);
      LOG ("analyzed %u", lit);
      marks[idx] = true;
      PUSH_STACK (citten->analyzed, idx);
    }
    if (next == SIZE_STACK (citten->analyzed))
      break;
    const unsigned idx = PEEK_STACK (citten->analyzed, next);
    next++;
    const kar *const v = vars + idx;
    assert (!v->level);
    ref = v->reason;
  }
  assert (EMPTY_STACK (citten->klause));
  ref = new_learned_klause (citten);
  ROG (ref, "registering final inconsistent empty");
  citten->inconsistent = ref;

  for (all_stack (unsigned, idx, *analyzed))
    marks[idx] = 0;

  CLEAR_STACK (*analyzed);
  CLEAR_STACK (*resolved);
}

static int propagate_units (citten *citten) {
  if (citten->inconsistent != INVALID)
    return 20;

  if (EMPTY_STACK (citten->units)) {
    LOG ("no root level unit clauses");
    return 0;
  }

  LOG ("propagating %zu root level unit clauses",
       SIZE_STACK (citten->units));

  const value *const values = citten->values;

  for (size_t next = 0; next < SIZE_STACK (citten->units); next++) {
    const unsigned ref = PEEK_STACK (citten->units, next);
    assert (ref != INVALID);
    klause *c = dereference_klause (citten, ref);
    assert (c->size == 1);
    ROG (ref, "propagating unit");
    const unsigned unit = c->lits[0];
    const value value = values[unit];
    if (value > 0)
      continue;
    if (value < 0) {
      inconsistent (citten, ref);
      return 20;
    }
    assign (citten, unit, ref);
  }
  const unsigned conflict = propagate (citten);
  if (conflict == INVALID)
    return 0;
  inconsistent (citten, conflict);
  return 20;
}

/*------------------------------------------------------------------------*/

static klause *begin_klauses (citten *citten) {
  return (klause *) BEGIN_STACK (citten->klauses);
}

static klause *end_original_klauses (citten *citten) {
  return (klause *) (BEGIN_STACK (citten->klauses) +
                     citten->end_original_ref);
}

static klause *end_klauses (citten *citten) {
  return (klause *) END_STACK (citten->klauses);
}

static klause *next_klause (citten *citten, klause *c) {
  assert (begin_klauses (citten) <= c);
  assert (c < end_klauses (citten));
  unsigned *res = c->lits + c->size;
  if (citten->antecedents && is_learned_klause (c))
    res += c->aux;
  return (klause *) res;
}

/*------------------------------------------------------------------------*/

static void reset_core (citten *citten) {
  LOG ("resetting core clauses");
  size_t reset = 0;
  for (all_klauses (c))
    if (is_core_klause (c))
      unset_core_klause (c), reset++;

#ifdef LOGGING
  LOG ("reset %zu core clauses", reset);
#else
  (void) reset;
#endif
  CLEAR_STACK (citten->core);
}

static void reset_implicant (citten *citten) {
  LOG ("resetting prime implicant");
  CLEAR_STACK (citten->prime);
  citten->last_klause_decision = SIZE_STACK (citten->original_klause_refs);
  CLEAR_STACK (citten->klause_decision_control);
}

static void reset_assumptions (citten *citten) {
  LOG ("reset %zu assumptions", SIZE_STACK (citten->assumptions));
  unsigned *q = BEGIN_STACK (citten->assumptions);
  const unsigned *end = END_STACK (citten->assumptions);
  while (q != end) {
    const unsigned assumption = *q++;
    citten->failed[assumption] = false;
  }
#ifndef NDEBUG
  for (size_t i = 0; i < citten->size; i++)
    assert (!citten->failed[i]);
#endif
  if (!citten->keep_assumptions)
    CLEAR_STACK (citten->assumptions);
  if (citten->failing != INVALID) {
    ROG (citten->failing, "reset failed assumption reason");
    citten->failing = INVALID;
  }
}

static void reset_incremental (citten *citten) {
  // if (citten->level)
  completely_backtrack_to_root_level (citten);
  if (!EMPTY_STACK (citten->assumptions))
    reset_assumptions (citten);
  else
    assert (citten->failing == INVALID);
  if (citten->status == 21)
    reset_core (citten);
  reset_implicant (citten);
  UPDATE_STATUS (0);
}

/*------------------------------------------------------------------------*/

static bool flip_literal (citten *citten, unsigned lit) {
  INC (citten_flip);
  signed char *values = citten->values;
  if (values[lit] < 0)
    lit ^= 1;
  LOG ("trying to flip value of satisfied literal %u", lit);
  assert (values[lit] > 0);
  katches *watches = citten->watches + lit;
  unsigned *q = BEGIN_STACK (*watches);
  const unsigned *const end_watches = END_STACK (*watches);
  unsigned const *p = q;
  uint64_t ticks =
      (((const char *const) end_watches - (const char *const) q) >> 7) + 1;
  bool res = true;
  while (p != end_watches) {
    const unsigned ref = *q++ = *p++;
    klause *c = dereference_klause (citten, ref);
    unsigned *lits = c->lits;
    const unsigned other = lits[0] ^ lits[1] ^ lit;
    const value other_value = values[other];
    ticks++;
    if (other_value > 0)
      continue;
    value replacement_value = -1;
    unsigned replacement = INVALID;
    const unsigned *const end_lits = lits + c->size;
    unsigned *r;
    for (r = lits + 2; r != end_lits; r++) {
      replacement = *r;
      assert (replacement != lit);
      replacement_value = values[replacement];
      assert (replacement_value);
      if (replacement_value > 0)
        break;
    }
    if (replacement_value > 0) {
      assert (replacement != INVALID);
      ROG (ref, "unwatching %u in", lit);
      lits[0] = other;
      lits[1] = replacement;
      *r = lit;
      watch_klause (citten, replacement, ref);
      q--;
    } else {
      assert (replacement_value < 0);
      ROG (ref, "single satisfied");
      res = false;
      break;
    }
  }
  while (p != end_watches)
    *q++ = *p++;
  SET_END_OF_STACK (*watches, q);
  ADD (citten_ticks, ticks);
  if (res) {
    LOG ("flipping value of %u", lit);
    values[lit] = -1;
    const unsigned not_lit = lit ^ 1;
    values[not_lit] = 1;
    INC (citten_flipped);
  } else
    LOG ("failed to flip value of %u", lit);
  return res;
}

/*------------------------------------------------------------------------*/

// this cadical specific clause addition avoids copying clauses multiple
// times just to convert literals to unsigned representation.
//
static unsigned int2u (int lit) {
  assert (lit != 0);
  int idx = abs (lit) - 1;
  return (lit < 0) + 2u * (unsigned) idx;
}
static int u2int (unsigned lit) {
  assert (lit != INVALID);
  int idx = (lit >> 1) + 1;
  if (lit & 1)
    idx = -idx;
  return idx;
}

void citten_assume (citten *citten, int elit) {
  REQUIRE_INITIALIZED ();
  if (citten->status)
    reset_incremental (citten);
  const unsigned ilit = import_literal (citten, elit);
  LOG ("registering assumption %u", ilit);
  PUSH_STACK (citten->assumptions, ilit);
}

void citten_assume_signed (citten *citten, int elit) {
  unsigned kelit = int2u (elit);
  citten_assume (citten, kelit);
}

void citten_clause_with_id_and_exception (citten *citten, unsigned id,
                                          size_t size, const int *elits,
                                          unsigned except) {
  REQUIRE_INITIALIZED ();
  if (citten->status)
    reset_incremental (citten);
  assert (EMPTY_STACK (citten->klause));
  const int *const end = elits + size;
  for (const int *p = elits; p != end; p++) {
    const unsigned elit = int2u (*p); // this is the conversion
    if (elit == except)
      continue;
    const unsigned ilit = import_literal (citten, elit);
    assert (ilit < citten->lits);
    const unsigned iidx = ilit / 2;
    if (citten->marks[iidx])
      INVALID_API_USAGE ("variable '%u' of literal '%u' occurs twice",
                         elit / 2, elit);
    citten->marks[iidx] = true;
    PUSH_STACK (citten->klause, ilit);
  }
  for (unsigned *p = citten->klause.begin; p != citten->klause.end; p++)
    citten->marks[*p / 2] = false;
  new_original_klause (citten, id);
  CLEAR_STACK (citten->klause);
}

void citten_clause_with_id_and_equivalence (citten *citten, unsigned id,
                                            size_t size, const int *elits,
                                            unsigned lit, unsigned other) {
  REQUIRE_INITIALIZED ();
  if (citten->status)
    reset_incremental (citten);
  assert (EMPTY_STACK (citten->klause));
  bool sat = false;
  const int *const end = elits + size;
  for (const int *p = elits; p != end; p++) {
    const unsigned elit = int2u (*p); // this is the conversion
    if (elit == (lit ^ 1u) || elit == (other ^ 1u))
      continue;
    if (elit == lit || elit == other) {
      sat = true;
      break;
    }
    const unsigned ilit = import_literal (citten, elit);
    assert (ilit < citten->lits);
    const unsigned iidx = ilit / 2;
    if (citten->marks[iidx])
      INVALID_API_USAGE ("variable '%u' of literal '%u' occurs twice",
                         elit / 2, elit);
    citten->marks[iidx] = true;
    PUSH_STACK (citten->klause, ilit);
  }
  for (unsigned *p = citten->klause.begin; p != citten->klause.end; p++)
    citten->marks[*p / 2] = false;
  if (!sat)
    new_original_klause (citten, id);
  CLEAR_STACK (citten->klause);
}

void citten_unit_with_id (citten *citten, unsigned id, int lit) {
  citten_clause_with_id_and_exception (citten, id, 1, &lit, INVALID);
}
void citten_clause (citten *citten, size_t size, int *elits) {
  citten_clause_with_id_and_exception (citten, INVALID, size, elits,
                                       INVALID);
}

void citten_clause_with_id (citten *citten, unsigned id, size_t size,
                            int *elits) {
  citten_clause_with_id_and_exception (citten, id, size, elits, INVALID);
}

void citten_unit (citten *citten, int lit) {
  citten_clause (citten, 1, &lit);
}

void citten_binary (citten *citten, int a, int b) {
  int clause[2] = {a, b};
  citten_clause (citten, 2, clause);
}

int citten_solve (citten *citten) {
  REQUIRE_INITIALIZED ();
  if (citten->status)
    reset_incremental (citten);
  else // if (citten->level)
    completely_backtrack_to_root_level (citten);

  LOG ("starting solving under %zu assumptions",
       SIZE_STACK (citten->assumptions));

  INC (citten_solved);

  int res = propagate_units (citten);
  while (!res) {
    const unsigned conflict = propagate (citten);
    if (citten->terminator &&
        citten->terminator (citten->terminator_data)) {
      LOG ("terminator requested termination");
      res = -1;
      break;
    }
    if (conflict != INVALID) {
      if (citten->level)
        analyze (citten, conflict);
      else {
        inconsistent (citten, conflict);
        res = 20;
      }
    } else
      res = decide (citten);
  }

  if (res < 0)
    res = 0;

  if (!res && !EMPTY_STACK (citten->assumptions))
    reset_assumptions (citten);

  UPDATE_STATUS (res);

  if (res == 10)
    INC (citten_sat);
  else if (res == 20)
    INC (citten_unsat);
  else
    INC (citten_unknown);

  LOG ("finished solving with result %d", res);

  return res;
}

int citten_solve_prime (citten *citten) {
  REQUIRE_INITIALIZED ();
  if (citten->status)
    reset_incremental (citten);
  else // if (citten->level)
    completely_backtrack_to_root_level (citten);

  LOG ("starting solving under %zu assumptions",
       SIZE_STACK (citten->assumptions));

  INC (citten_solved);

  int res = propagate_units (citten);
  while (!res) {
    const unsigned conflict = propagate (citten);
    if (citten->terminator &&
        citten->terminator (citten->terminator_data)) {
      LOG ("terminator requested termination");
      res = -1;
      break;
    }
    if (conflict != INVALID) {
      if (citten->level)
        analyze (citten, conflict);
      else {
        inconsistent (citten, conflict);
        res = 20;
      }
    } else
      res = decide_next_clause (citten);
  }

  if (res < 0)
    res = 0;

  if (!res && !EMPTY_STACK (citten->assumptions))
    reset_assumptions (citten);

  if (res == 11) {
    unsigneds *prime = &citten->prime;
    const value *const values = citten->values;
    // push on prime implicant stack.
    // TODO: improve
    for (all_kits (lit)) {
      if (values[lit] > 0) {
        LOG ("pushing prime %zd = %d", lit, export_literal (citten, lit));
        PUSH_STACK (*prime, export_literal (citten, lit));
      }
    }
  }
  UPDATE_STATUS (res);

  if (res == 10)
    INC (citten_sat);
  else if (res == 11)
    INC (citten_implicant);
  else if (res == 20)
    INC (citten_unsat);
  else
    INC (citten_unknown);

  LOG ("finished solving with result %d", res);

  return res;
}

int citten_status (citten *citten) { return citten->status; }

unsigned citten_compute_clausal_core (citten *citten,
                                      uint64_t *learned_ptr) {
  REQUIRE_STATUS (20);

  if (!citten->antecedents)
    INVALID_API_USAGE ("antecedents not tracked");

  LOG ("computing clausal core");

  unsigneds *resolved = &citten->resolved;
  assert (EMPTY_STACK (*resolved));

  unsigned original = 0;
  uint64_t learned = 0;

  unsigned reason_ref = citten->inconsistent;

  if (reason_ref == INVALID) {
    assert (!EMPTY_STACK (citten->assumptions));
    reason_ref = citten->failing;
    if (reason_ref == INVALID) {
      LOG ("assumptions mutually inconsistent");
      goto DONE;
    }
  }

  PUSH_STACK (*resolved, reason_ref);
  unsigneds *core = &citten->core;
  assert (EMPTY_STACK (*core));

  while (!EMPTY_STACK (*resolved)) {
    const unsigned c_ref = POP_STACK (*resolved);
    if (c_ref == INVALID) {
      const unsigned d_ref = POP_STACK (*resolved);
      ROG (d_ref, "core[%zu]", SIZE_STACK (*core));
      PUSH_STACK (*core, d_ref);
      klause *d = dereference_klause (citten, d_ref);
      assert (!is_core_klause (d));
      set_core_klause (d);
      if (is_learned_klause (d))
        learned++;
      else
        original++;
    } else {
      klause *c = dereference_klause (citten, c_ref);
      if (is_core_klause (c))
        continue;
      PUSH_STACK (*resolved, c_ref);
      PUSH_STACK (*resolved, INVALID);
      ROG (c_ref, "analyzing antecedent core");
      if (!is_learned_klause (c))
        continue;
      for (all_antecedents (d_ref, c)) {
        klause *d = dereference_klause (citten, d_ref);
        if (!is_core_klause (d))
          PUSH_STACK (*resolved, d_ref);
      }
    }
  }

DONE:

  if (learned_ptr)
    *learned_ptr = learned;

  LOG ("clausal core of %u original clauses", original);
  LOG ("clausal core of %" PRIu64 " learned clauses", learned);
  citten->statistics.original = original;
  citten->statistics.learned = 0;
  UPDATE_STATUS (21);

  return original;
}

void citten_traverse_core_ids (citten *citten, void *state,
                               void (*traverse) (void *, unsigned)) {
  REQUIRE_STATUS (21);

  LOG ("traversing core of original clauses");

  unsigned traversed = 0;

  for (all_original_klauses (c)) {
    // only happens for 'true' incremental calls, i.e. if add happens after
    // solve
    if (is_learned_klause (c))
      continue;
    if (!is_core_klause (c))
      continue;
    ROG (reference_klause (citten, c), "traversing");
    traverse (state, c->aux);
    traversed++;
  }

  LOG ("traversed %u original core clauses", traversed);
  (void) traversed;

  assert (citten->status == 21);
}

void citten_traverse_core_clauses (citten *citten, void *state,
                                   void (*traverse) (void *, bool, size_t,
                                                     const unsigned *)) {
  REQUIRE_STATUS (21);

  LOG ("traversing clausal core");

  unsigned traversed = 0;

  for (all_stack (unsigned, c_ref, citten->core)) {
    klause *c = dereference_klause (citten, c_ref);
    assert (is_core_klause (c));
    const bool learned = is_learned_klause (c);
    unsigneds *eclause = &citten->eclause;
    assert (EMPTY_STACK (*eclause));
    for (all_literals_in_klause (ilit, c)) {
      const unsigned elit = export_literal (citten, ilit);
      PUSH_STACK (*eclause, elit);
    }
    const size_t size = SIZE_STACK (*eclause);
    const unsigned *elits = eclause->begin;
    ROG (reference_klause (citten, c), "traversing");
    traverse (state, learned, size, elits);
    CLEAR_STACK (*eclause);
    traversed++;
  }

  LOG ("traversed %u core clauses", traversed);
  (void) traversed;

  assert (citten->status == 21);
}

void citten_traverse_core_clauses_with_id (
    citten *citten, void *state,
    void (*traverse) (void *state, unsigned, bool learned, size_t,
                      const unsigned *)) {
  REQUIRE_STATUS (21);

  LOG ("traversing clausal core");

  unsigned traversed = 0;

  for (all_stack (unsigned, c_ref, citten->core)) {
    klause *c = dereference_klause (citten, c_ref);
    assert (is_core_klause (c));
    const bool learned = is_learned_klause (c);
    unsigneds *eclause = &citten->eclause;
    assert (EMPTY_STACK (*eclause));
    for (all_literals_in_klause (ilit, c)) {
      const unsigned elit = export_literal (citten, ilit);
      PUSH_STACK (*eclause, elit);
    }
    const size_t size = SIZE_STACK (*eclause);
    const unsigned *elits = eclause->begin;
    ROG (reference_klause (citten, c), "traversing");
    unsigned ctag = learned ? 0 : c->aux;
    traverse (state, ctag, learned, size, elits);
    CLEAR_STACK (*eclause);
    traversed++;
  }

  LOG ("traversed %u core clauses", traversed);
  (void) traversed;

  assert (citten->status == 21);
}

void citten_trace_core (citten *citten, void *state,
                        void (*trace) (void *, unsigned, unsigned, bool,
                                       size_t, const unsigned *, size_t,
                                       const unsigned *)) {
  REQUIRE_STATUS (21);

  LOG ("tracing clausal core");

  unsigned traced = 0;

  for (all_stack (unsigned, c_ref, citten->core)) {
    klause *c = dereference_klause (citten, c_ref);
    assert (is_core_klause (c));
    const bool learned = is_learned_klause (c);
    unsigneds *eclause = &citten->eclause;
    assert (EMPTY_STACK (*eclause));
    for (all_literals_in_klause (ilit, c)) {
      const unsigned elit = export_literal (citten, ilit);
      PUSH_STACK (*eclause, elit);
    }
    const size_t size = SIZE_STACK (*eclause);
    const unsigned *elits = eclause->begin;

    unsigneds *resolved = &citten->resolved;
    assert (EMPTY_STACK (*resolved));
    if (learned) {
      for (all_antecedents (ref, c)) {
        PUSH_STACK (*resolved, ref);
      }
    }
    const size_t rsize = SIZE_STACK (*resolved);
    const unsigned *rids = resolved->begin;

    unsigned cid = reference_klause (citten, c);
    unsigned ctag = learned ? 0 : c->aux;
    ROG (cid, "tracing");
    trace (state, cid, ctag, learned, size, elits, rsize, rids);
    CLEAR_STACK (*eclause);
    CLEAR_STACK (*resolved);
    traced++;
  }

  LOG ("traced %u core clauses", traced);
  (void) traced;

  assert (citten->status == 21);
}

void citten_shrink_to_clausal_core (citten *citten) {
  REQUIRE_STATUS (21);

  LOG ("shrinking formula to core of original clauses");

  CLEAR_STACK (citten->trail);

  citten->unassigned = citten->lits / 2;
  citten->propagated = 0;
  citten->level = 0;

  update_search (citten, citten->queue.last);

  memset (citten->values, 0, citten->lits);

  for (all_kits (lit))
    CLEAR_STACK (KATCHES (lit));

  assert (citten->inconsistent != INVALID);
  klause *inconsistent = dereference_klause (citten, citten->inconsistent);
  if (is_learned_klause (inconsistent) || inconsistent->size) {
    ROG (citten->inconsistent, "resetting inconsistent");
    citten->inconsistent = INVALID;
  } else
    ROG (citten->inconsistent, "keeping inconsistent");

  CLEAR_STACK (citten->units);

  klause *begin = begin_klauses (citten), *q = begin;
  klause const *const end = end_original_klauses (citten);
#ifdef LOGGING
  unsigned original = 0;
#endif
  for (klause *c = begin, *next; c != end; c = next) {
    next = next_klause (citten, c);
    // assert (!is_learned_klause (c)); not necessarily true
    if (is_learned_klause (c))
      continue;
    if (!is_core_klause (c))
      continue;
    unset_core_klause (c);
    const unsigned dst = (unsigned *) q - (unsigned *) begin;
    const unsigned size = c->size;
    if (!size) {
      if (citten->inconsistent != INVALID)
        citten->inconsistent = dst;
    } else if (size == 1) {
      PUSH_STACK (citten->units, dst);
      ROG (dst, "keeping");
    } else {
      watch_klause (citten, c->lits[0], dst);
      watch_klause (citten, c->lits[1], dst);
    }
    if (c == q)
      q = next;
    else {
      const size_t bytes = (char *) next - (char *) c;
      memmove (q, c, bytes);
      q = (klause *) ((char *) q + bytes);
    }
#ifdef LOGGING
    original++;
#endif
  }
  SET_END_OF_STACK (citten->klauses, (unsigned *) q);
  citten->end_original_ref = SIZE_STACK (citten->klauses);
  LOG ("end of original clauses at %zu", citten->end_original_ref);
  LOG ("%u original clauses left", original);

  CLEAR_STACK (citten->core);

  UPDATE_STATUS (0);
}

signed char citten_signed_value (citten *citten, int selit) {
  REQUIRE_SATISFIED_STATUS ();
  const unsigned elit = int2u (selit);
  const unsigned eidx = elit / 2;
  if (eidx >= citten->evars)
    return 0;
  unsigned iidx = citten->import[eidx];
  if (!iidx)
    return 0;
  const unsigned ilit = 2 * (iidx - 1) + (elit & 1);
  return citten->values[ilit];
}

signed char citten_value (citten *citten, unsigned elit) {
  REQUIRE_SATISFIED_STATUS ();
  const unsigned eidx = elit / 2;
  if (eidx >= citten->evars)
    return 0;
  unsigned iidx = citten->import[eidx];
  if (!iidx)
    return 0;
  const unsigned ilit = 2 * (iidx - 1) + (elit & 1);
  return citten->values[ilit];
}

signed char citten_fixed (citten *citten, unsigned elit) {
  const unsigned eidx = elit / 2;
  if (eidx >= citten->evars)
    return 0;
  unsigned iidx = citten->import[eidx];
  if (!iidx)
    return 0;
  iidx--;
  const unsigned ilit = 2 * iidx + (elit & 1);
  signed char res = citten->values[ilit];
  if (!res)
    return 0;
  kar *v = citten->vars + iidx;
  if (v->level)
    return 0;
  return res;
}

signed char citten_implied (citten *citten, unsigned elit) {
  REQUIRE_STATUS (10);
  const unsigned eidx = elit / 2;
  if (eidx >= citten->evars)
    return 0;
  unsigned iidx = citten->import[eidx];
  if (!iidx)
    return 0;
  iidx--;
  const unsigned ilit = 2 * iidx + (elit & 1);
  signed char res = citten->values[ilit];
  if (!res)
    return 0;
  kar *v = citten->vars + iidx;
  if (v->level > SIZE_STACK (citten->assumptions))
    return 0;
  return res;
}
signed char citten_implied_signed (citten *citten, int signed_elit) {
  unsigned elit = int2u (signed_elit);
  return citten_implied (citten, elit);
}

signed char citten_fixed_signed (citten *citten, int elit) {
  unsigned kelit = int2u (elit);
  return citten_fixed (citten, kelit);
}

bool citten_flip_literal (citten *citten, unsigned elit) {
  REQUIRE_STATUS (10);
  const unsigned eidx = elit / 2;
  if (eidx >= citten->evars)
    return false;
  unsigned iidx = citten->import[eidx];
  if (!iidx)
    return false;
  const unsigned ilit = 2 * (iidx - 1) + (elit & 1);
  if (citten_fixed (citten, elit))
    return false;
  if (citten_implied (citten, elit))
    return false;
  return flip_literal (citten, ilit);
}

bool citten_flip_signed_literal (citten *citten, int elit) {
  REQUIRE_STATUS (10);
  unsigned kelit = int2u (elit);
  return citten_flip_literal (citten, kelit);
}

bool citten_failed (citten *citten, unsigned elit) {
  REQUIRE_STATUS (20);
  const unsigned eidx = elit / 2;
  if (eidx >= citten->evars)
    return false;
  unsigned iidx = citten->import[eidx];
  if (!iidx)
    return false;
  const unsigned ilit = 2 * (iidx - 1) + (elit & 1);
  return citten->failed[ilit];
}

bool citten_failed_signed (citten *citten, int elit) {
  REQUIRE_STATUS (20);
  unsigned kelit = int2u (elit);
  return citten_failed (citten, kelit);
}

// checks both watches for clauses with only one literal positively
// assigned. If such a clause is found, return false. Otherwise fix watch
// invariant and return true
static bool prime_propagate (citten *citten, const unsigned idx) {
  unsigned lit = 2 * idx;
  unsigned conflict = INVALID;
  value *values = citten->values;
  for (int i = 0; i < 2; i++) {
    if (conflict != INVALID)
      break;
    lit = lit ^ i;
    const unsigned not_lit = lit ^ 1;
    katches *watches = citten->watches + not_lit;
    unsigned *q = BEGIN_STACK (*watches);
    const unsigned *const end_watches = END_STACK (*watches);
    unsigned const *p = q;
    uint64_t ticks =
        (((const char *const) end_watches - (const char *const) q) >> 7) +
        1;
    while (p != end_watches) {
      const unsigned ref = *q++ = *p++;
      klause *c = dereference_klause (citten, ref);
      if (is_learned_klause (c))
        continue;
      assert (c->size > 1);
      unsigned *lits = c->lits;
      const unsigned other = lits[0] ^ lits[1] ^ not_lit;
      const value other_value = values[other];
      ticks++;
      if (other_value > 0)
        continue;
      value replacement_value = -1;
      unsigned replacement = INVALID;
      const unsigned *const end_lits = lits + c->size;
      unsigned *r;
      for (r = lits + 2; r != end_lits; r++) {
        replacement = *r;
        replacement_value = values[replacement];
        if (replacement_value > 0)
          break;
      }
      if (replacement_value > 0) {
        assert (replacement != INVALID);
        ROG (ref, "unwatching %u in", not_lit);
        lits[0] = other;
        lits[1] = replacement;
        *r = not_lit;
        watch_klause (citten, replacement, ref);
        q--;
      } else {
        ROG (ref, "idx %u forced prime by", idx);
        conflict = ref;
        break;
      }
    }
    while (p != end_watches)
      *q++ = *p++;
    SET_END_OF_STACK (*watches, q);
    ADD (citten_ticks, ticks);
  }
  return conflict == INVALID;
}

unsigned citten_size_implicant (citten *citten) {
  REQUIRE_STATUS (11);
  return SIZE_STACK (citten->prime);
}

// Compute a subset of the current model that satisfies all
// original clauses.
// TODO does not work if flip has been called beforehand
void citten_compute_prime_implicant (citten *citten) {
  REQUIRE_STATUS (10);

  INC (citten_implicant);
  value *values = citten->values;
  kar *vars = citten->vars;
#ifndef NDEBUG
  bool limit_hit = 0;
#endif
  const unsigned assumption_levels = SIZE_STACK (citten->assumptions);
  assert (EMPTY_STACK (citten->prime));
  for (backwards_stack (unsigned, lit, citten->trail)) {
    if (CITTEN_TICKS >= citten->limits.ticks) {
      LOG ("ticks limit %" PRIu64 " hit after %" PRIu64 " ticks",
           citten->limits.ticks, CITTEN_TICKS);
#ifndef NDEBUG
      limit_hit = 1;
#endif
      break;
    }
    // assert (values[lit] > 0);
    const unsigned idx = lit / 2;
    const unsigned ref = vars[idx].reason;
    assert (vars[idx].level);
    klause *c = 0;
    if (ref != INVALID)
      c = dereference_klause (citten, ref);
    if (ref == INVALID && vars[idx].level <= assumption_levels)
      break;
    if (ref == INVALID || is_learned_klause (c)) {
      LOG ("non-prime candidate var %d", idx);
      assert (vars[idx].level >= assumption_levels);
      if (prime_propagate (citten, idx)) {
        values[lit] = 0;
        values[lit ^ 1] = 0;
      }
      // else assert (values[lit] > 0);
      // breaks if citten_flip happens before.
    }
  }
  unsigneds *prime = &citten->prime;
  // push on prime implicant stack.
  for (all_kits (lit)) {
    if (values[lit] > 0) {
      LOG ("pushing prime %zd = %d", lit, export_literal (citten, lit));
      PUSH_STACK (*prime, export_literal (citten, lit));
    }
  }
  // TODO: check if we are able to use partial results (if limit_hit).
  assert (!EMPTY_STACK (citten->prime) || limit_hit);
  UPDATE_STATUS (11);

  /*
  int res = SIZE_STACK (citten->prime);
  return res;
  */
}

int citten_next_signed_implicant (citten *citten, size_t idx) {
  REQUIRE_STATUS (11);
  const unsigneds *const prime = &citten->prime;
  if (idx >= SIZE_STACK (*prime))
    return 0;
  // already exported
  return u2int (PEEK_STACK (*prime, idx));
}

void citten_bump_signed_literal (citten *citten, int signed_elit) {
  const unsigned elit = int2u (signed_elit);
  const unsigned eidx = elit / 2;
  if (eidx >= citten->evars)
    return;
  unsigned iidx = citten->import[eidx];
  if (!iidx)
    return;
  iidx--;
  // completely_backtrack_to_root_level (citten);
  LOG ("bumping signed external literal %d = %d (=%d) = %d", signed_elit,
       elit, eidx, iidx);
  INC (citten_bumped);
  dequeue (citten, iidx);
  enqueue (citten, iidx);
  update_search (citten, iidx);
  // UPDATE_STATUS (0);
}

void citten_phase_signed_literal (citten *citten, int signed_elit) {
  const unsigned elit = int2u (signed_elit);
  const unsigned eidx = elit / 2;
  if (eidx >= citten->evars)
    return;
  unsigned iidx = citten->import[eidx];
  if (!iidx)
    return;
  iidx--;
  const unsigned sign = elit & 1;
  // completely_backtrack_to_root_level (citten);
  LOG ("phase signed external literal %d = %d (=%d) = %d sign %d",
       signed_elit, elit, eidx, iidx, sign);
  INC (citten_phase);
  citten->phases[iidx] = sign;
  // UPDATE_STATUS (0);
}
