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

citten *citten_init (void);
void citten_clear (citten *);
void citten_release (citten *);

#ifdef LOGGING
void citten_set_logging (citten *citten);
#endif

void citten_track_antecedents (citten *);

void citten_shuffle_clauses (citten *);
void citten_flip_phases (citten *);
void citten_randomize_phases (citten *);

void citten_assume (citten *, unsigned lit);
void citten_assume_signed (citten *, int lit);

void citten_clause (citten *, size_t size, unsigned *);

void citten_unit (citten *, unsigned);
void citten_binary (citten *, unsigned, unsigned);

void citten_clause_with_id (citten *, unsigned id, size_t size, int *);
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
int citten_status (citten *);

signed char citten_value (citten *, unsigned);
signed char citten_signed_value (citten *, int); // converts second argument
signed char citten_fixed (citten *, unsigned);
signed char citten_fixed_signed (citten *,
                                 int); // converts
bool citten_failed (citten *, unsigned);
bool citten_flip_literal (citten *, unsigned);
bool citten_flip_signed_literal (citten *, int);

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

#ifdef __cplusplus
}
#endif

#endif
