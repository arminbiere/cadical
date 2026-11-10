#ifndef _citten_h_INCLUDED
#define _citten_h_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct citten citten;

struct citten_statistics {
  uint64_t learned;
  uint64_t original;
  uint64_t citten_flip;
  uint64_t citten_flipped;
  uint64_t citten_sat;
  uint64_t citten_solved;
  uint64_t citten_conflicts;
  uint64_t citten_decisions;
  uint64_t citten_propagations;
  uint64_t citten_bumped;
  uint64_t citten_phase;
  uint64_t citten_implicant;
  uint64_t citten_ticks;
  uint64_t citten_unknown;
  uint64_t citten_unsat;
};

citten *citten_init (void);
void citten_clear (citten *);
void citten_release (citten *);
void citten_restart (citten *);
struct citten_statistics *citten_get_statistics (citten *);

#ifdef LOGGING
void citten_set_logging (citten *citten);
#endif

void citten_track_antecedents (citten *);
void citten_keep_assumptions (citten *);

void citten_shuffle_clauses (citten *);
void citten_flip_phases (citten *);
void citten_randomize_phases (citten *);

void citten_assume (citten *, int lit);
void citten_assume_signed (citten *, int lit);

void citten_unit (citten *, int);
void citten_binary (citten *, int, int);

void citten_clause (citten *, size_t size, int *);
void citten_clause_with_id (citten *, unsigned id, size_t size, int *);
void citten_unit_with_id (citten *, unsigned id, int);
void citten_unit_with_id_ignore_prime (citten *, unsigned id, int);
void citten_clause_with_id_and_exception (citten *, unsigned id,
                                          size_t size, const int *,
                                          unsigned except);
void citten_clause_with_id_and_equivalence (citten *, unsigned id,
                                            size_t size, const int *,
                                            unsigned, unsigned);

void citten_no_ticks_limit (citten *);
void citten_set_ticks_limit (citten *, uint64_t);
uint64_t citten_current_ticks (citten *);

void citten_no_terminator (citten *);
void citten_set_terminator (citten *, void *, int (*) (void *));

int citten_solve (citten *);
int citten_solve_prime (citten *);
int citten_status (citten *);

signed char citten_value (citten *, unsigned);
signed char citten_signed_value (citten *, int); // converts second argument
signed char citten_fixed (citten *, unsigned);
signed char citten_fixed_signed (citten *,
                                 int); // converts
bool citten_failed (citten *, unsigned);
bool citten_failed_signed (citten *, int);
bool citten_flip_literal (citten *, unsigned);
bool citten_flip_signed_literal (citten *, int);
signed char citten_implied (citten *, unsigned);
signed char citten_implied_signed (citten *, int);

void citten_bump_signed_literal (citten *, int);
void citten_phase_signed_literal (citten *, int);

unsigned citten_compute_clausal_core (citten *, uint64_t *learned);
void citten_shrink_to_clausal_core (citten *);

void citten_traverse_core_ids (citten *, void *state,
                               void (*traverse) (void *state, unsigned id));

void citten_traverse_core_clauses (citten *, void *state,
                                   void (*traverse) (void *state,
                                                     bool learned, size_t,
                                                     const unsigned *));
void citten_traverse_core_clauses_with_id (
    citten *, void *state,
    void (*traverse) (void *state, unsigned, bool learned, size_t,
                      const unsigned *));
void citten_trace_core (citten *, void *state,
                        void (*trace) (void *, unsigned, unsigned, bool,
                                       size_t, const unsigned *, size_t,
                                       const unsigned *));
unsigned citten_size_implicant (citten *);

void citten_compute_prime_implicant (citten *);
int citten_next_signed_implicant (citten *, size_t);

#ifdef __cplusplus
}
#endif

#endif
