#ifndef _ccadical_h_INCLUDED
#define _ccadical_h_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef __cplusplus
extern "C" {
#endif
/*------------------------------------------------------------------------*/

#include <stddef.h>
#include <stdint.h>

// C wrapper for CaDiCaL's C++ API following IPASIR.

typedef struct CCaDiCaL CCaDiCaL;

const char *ccadical_signature (void);
CCaDiCaL *ccadical_init (void);
void ccadical_release (CCaDiCaL *);

void ccadical_add (CCaDiCaL *, int lit);
void ccadical_assume (CCaDiCaL *, int lit);
int ccadical_solve (CCaDiCaL *);
int ccadical_val (CCaDiCaL *, int lit);
int ccadical_failed (CCaDiCaL *, int lit);

void ccadical_set_terminate (CCaDiCaL *, void *state,
                             int (*terminate) (void *state));

void ccadical_set_learn (CCaDiCaL *, void *state, int max_length,
                         void (*learn) (void *state, int *clause));

/*------------------------------------------------------------------------*/

// C wrapper for CaDiCaL's C++ API following IPASIR-UP.

typedef struct CCaDiCaLPropagator CCaDiCaLPropagator;

void ccadical_connect_external_propagator (CCaDiCaL *,
                                           CCaDiCaLPropagator *);
void ccadical_disconnect_external_propagator (CCaDiCaL *);

void ccadical_add_observed_var (CCaDiCaL *, int var);
void ccadical_remove_observed_var (CCaDiCaL *, int var);
void ccadical_reset_observed_vars (CCaDiCaL *);
bool ccadical_is_decision (CCaDiCaL *, int lit);

void ccadical_phase (CCaDiCaL *, int lit);
void ccadical_unphase (CCaDiCaL *, int lit);

CCaDiCaLPropagator *ccadical_prop_init (void *state);
void ccadical_prop_release (CCaDiCaLPropagator *);
void ccadical_prop_lazy (CCaDiCaLPropagator *, bool is_lazy);

void ccadical_prop_set_notify_assignment (
    CCaDiCaLPropagator *,
    void (*notify_assignment) (void *state, int lit, bool is_fixed));
void ccadical_prop_set_notify_new_decision_level (
    CCaDiCaLPropagator *, void (*notify_new_decision_level) (void *state));
void ccadical_prop_set_notify_backtrack (
    CCaDiCaLPropagator *,
    void (*notify_backtrack) (void *state, size_t new_level));

void ccadical_prop_set_check_model (CCaDiCaLPropagator *,
                                    bool (*check_model) (void *state,
                                                         size_t size,
                                                         const int *model));
void ccadical_prop_set_decide (CCaDiCaLPropagator *,
                               int (*decide) (void *state));
void ccadical_prop_set_propagate (CCaDiCaLPropagator *,
                                  int (*propagate) (void *state));

void ccadical_prop_set_add_reason_clause_lit (
    CCaDiCaLPropagator *,
    int (*add_reason_clause_lit) (void *state, int propagated_lit));

void ccadical_prop_set_has_external_clause (
    CCaDiCaLPropagator *, bool (*has_external_clause) (void *state));
void ccadical_prop_set_add_external_clause_lit (
    CCaDiCaLPropagator *, int (*add_external_clause_lit) (void *state));

/*------------------------------------------------------------------------*/

// Non-IPASIR conformant 'C' functions.

void ccadical_constrain (CCaDiCaL *, int lit);
int ccadical_constraint_failed (CCaDiCaL *);
void ccadical_set_option (CCaDiCaL *, const char *name, int val);
void ccadical_limit (CCaDiCaL *, const char *name, int limit);
int ccadical_get_option (CCaDiCaL *, const char *name);
void ccadical_print_statistics (CCaDiCaL *);
int64_t ccadical_active (CCaDiCaL *);
int64_t ccadical_irredundant (CCaDiCaL *);
int ccadical_fixed (CCaDiCaL *, int lit);
void ccadical_terminate (CCaDiCaL *);
void ccadical_freeze (CCaDiCaL *, int lit);
int ccadical_frozen (CCaDiCaL *, int lit);
void ccadical_melt (CCaDiCaL *, int lit);
int ccadical_simplify (CCaDiCaL *);

/*------------------------------------------------------------------------*/

// Support legacy names used before moving to more IPASIR conforming names.

#define ccadical_reset ccadical_release
#define ccadical_sat ccadical_solve
#define ccadical_deref ccadical_val

/*------------------------------------------------------------------------*/
#ifdef __cplusplus
}
#endif
/*------------------------------------------------------------------------*/

#endif
