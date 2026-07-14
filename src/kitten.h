#ifndef _kitten_h_INCLUDED
#define _kitten_h_INCLUDED

#include "kitten-config.h"
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#ifdef __cplusplus
extern "C" {
#endif

#ifndef KITTEN_NAMESPACE
#define KITTEN_NAMESPACE(f) f
#endif

typedef struct kitten kitten;

kitten *KITTEN_NAMESPACE(kitten_init) (void);
void KITTEN_NAMESPACE(kitten_clear) (kitten *);
void KITTEN_NAMESPACE(kitten_release) (kitten *);

#ifdef LOGGING
void KITTEN_NAMESPACE(kitten_set_logging) (kitten *kitten);
#endif

void KITTEN_NAMESPACE(kitten_track_antecedents) (kitten *);

void KITTEN_NAMESPACE(kitten_shuffle_clauses) (kitten *);
void KITTEN_NAMESPACE(kitten_flip_phases) (kitten *);
void KITTEN_NAMESPACE(kitten_randomize_phases) (kitten *);

void KITTEN_NAMESPACE(kitten_assume) (kitten *, unsigned lit);
void KITTEN_NAMESPACE(kitten_assume_signed) (kitten *, int lit);

void KITTEN_NAMESPACE(kitten_clause) (kitten *, size_t size, unsigned *);
void KITTEN_NAMESPACE(citten_clause_with_id) (kitten *, unsigned id, size_t size, int *);
void KITTEN_NAMESPACE(kitten_unit) (kitten *, unsigned);
void KITTEN_NAMESPACE(kitten_binary) (kitten *, unsigned, unsigned);

void KITTEN_NAMESPACE(kitten_clause_with_id_and_exception) (kitten *, unsigned id,
                                          size_t size, const unsigned *,
                                          unsigned except);

void KITTEN_NAMESPACE(citten_clause_with_id_and_exception) (kitten *, unsigned id,
                                          size_t size, const int *,
                                          unsigned except);
void KITTEN_NAMESPACE(citten_clause_with_id_and_equivalence) (kitten *, unsigned id,
                                            size_t size, const int *,
                                            unsigned, unsigned);
void KITTEN_NAMESPACE(kitten_no_ticks_limit) (kitten *);
void KITTEN_NAMESPACE(kitten_set_ticks_limit) (kitten *, uint64_t);
uint64_t KITTEN_NAMESPACE(kitten_current_ticks) (kitten *);

void KITTEN_NAMESPACE(kitten_no_terminator) (kitten *);
void KITTEN_NAMESPACE(kitten_set_terminator) (kitten *, void *, int (*) (void *));

int KITTEN_NAMESPACE(kitten_solve) (kitten *);
int KITTEN_NAMESPACE(kitten_status) (kitten *);

signed char KITTEN_NAMESPACE(kitten_value) (kitten *, unsigned);
signed char KITTEN_NAMESPACE(kitten_signed_value) (kitten *, int); // converts second argument
signed char KITTEN_NAMESPACE(kitten_fixed) (kitten *, unsigned);
signed char KITTEN_NAMESPACE(kitten_fixed_signed) (kitten *, int); // converts
bool KITTEN_NAMESPACE(kitten_failed) (kitten *, unsigned);
bool KITTEN_NAMESPACE(kitten_flip_literal) (kitten *, unsigned);
bool KITTEN_NAMESPACE(kitten_flip_signed_literal) (kitten *, int);

unsigned KITTEN_NAMESPACE(kitten_compute_clausal_core) (kitten *, uint64_t *learned);
void KITTEN_NAMESPACE(kitten_shrink_to_clausal_core) (kitten *);

void KITTEN_NAMESPACE(kitten_traverse_core_ids) (kitten *, void *state,
                               void (*traverse) (void *state, unsigned id));

void KITTEN_NAMESPACE(kitten_traverse_core_clauses) (kitten *, void *state,
                                   void (*traverse) (void *state,
                                                     bool learned, size_t,
                                                     const unsigned *));
void KITTEN_NAMESPACE(kitten_traverse_core_clauses_with_id) (
    kitten *, void *state,
    void (*traverse) (void *state, unsigned, bool learned, size_t,
                      const unsigned *));
void KITTEN_NAMESPACE(kitten_trace_core) (kitten *, void *state,
                        void (*trace) (void *, unsigned, unsigned, bool,
                                       size_t, const unsigned *, size_t,
                                       const unsigned *));

#ifdef __cplusplus
}
#endif

#endif
