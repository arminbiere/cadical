#ifndef _ccadical_h_INCLUDED
#define _ccadical_h_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef __cplusplus
extern "C" {
#endif
/*------------------------------------------------------------------------*/

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

// C wrapper for CaDiCaL's C++ API following IPASIR.

typedef struct CCaDiCaL CCaDiCaL;

struct COption {
  const char *name;
  int def, lo, hi;
};

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
void ccadical_set_learn2 (CCaDiCaL *, void *state, int max_length,
                          void (*learn) (void *state, int32_t const *clause,
                                         int, void *));

void ccadical_set_fixed_listener (CCaDiCaL *ptr, void *state,
                                  void (*fixed) (void *state, int fixed));
/*------------------------------------------------------------------------*/

// Non-IPASIR conformant 'C' functions.

size_t ccadical_constrain (CCaDiCaL *, int lit);
bool ccadical_constraint_failed (CCaDiCaL *, size_t idx);
void ccadical_set_option (CCaDiCaL *, const char *name, int val);
struct COption *ccadical_options (CCaDiCaL *wrapper, size_t *len);
void ccadical_limit (CCaDiCaL *, const char *name, int limit);
int ccadical_get_option (CCaDiCaL *, const char *name);
void ccadical_print_statistics (CCaDiCaL *);
int64_t ccadical_active (CCaDiCaL *);
int64_t ccadical_irredundant (CCaDiCaL *);
int ccadical_fixed (CCaDiCaL *, int lit);
int ccadical_trace_proof (CCaDiCaL *, FILE *, const char *);
void ccadical_close_proof (CCaDiCaL *);
void ccadical_conclude (CCaDiCaL *);
void ccadical_terminate (CCaDiCaL *);
void ccadical_freeze (CCaDiCaL *, int lit);
int ccadical_frozen (CCaDiCaL *, int lit);
void ccadical_melt (CCaDiCaL *, int lit);
int ccadical_simplify (CCaDiCaL *);
int ccadical_vars (CCaDiCaL *);
int ccadical_declare_more_variables (CCaDiCaL *, int number_of_vars);
int ccadical_declare_one_more_variable (CCaDiCaL *);
void ccadical_phase (CCaDiCaL *wrapper, int lit);
void ccadical_unphase (CCaDiCaL *wrapper, int lit);

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
