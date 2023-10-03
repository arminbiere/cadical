#include "ipasir.h"
#include "ccadical.h"
#include "ipasir_up.h"

extern "C" {

const char *ipasir_signature () { return ccadical_signature (); }

void *ipasir_init () { return ccadical_init (); }

void ipasir_release (void *solver) {
  ccadical_release ((CCaDiCaL *) solver);
}

void ipasir_add (void *solver, int lit) {
  ccadical_add ((CCaDiCaL *) solver, lit);
}

void ipasir_assume (void *solver, int lit) {
  ccadical_assume ((CCaDiCaL *) solver, lit);
}

int ipasir_solve (void *solver) {
  return ccadical_solve ((CCaDiCaL *) solver);
}

int ipasir_val (void *solver, int lit) {
  return ccadical_val ((CCaDiCaL *) solver, lit);
}

int ipasir_failed (void *solver, int lit) {
  return ccadical_failed ((CCaDiCaL *) solver, lit);
}

void ipasir_set_terminate (void *solver, void *state,
                           int (*terminate) (void *state)) {
  ccadical_set_terminate ((CCaDiCaL *) solver, state, terminate);
}

void ipasir_set_learn (void *solver, void *state, int max_length,
                       void (*learn) (void *state, int *clause)) {
  ccadical_set_learn ((CCaDiCaL *) solver, state, max_length, learn);
}

void ipasir_connect_external_propagator (void *solver, void *propagator) {
  ccadical_connect_external_propagator ((CCaDiCaL *) solver,
                                        (CCaDiCaLPropagator *) propagator);
}
void ipasir_disconnect_external_propagator (void *solver) {
  ccadical_disconnect_external_propagator ((CCaDiCaL *) solver);
}

void ipasir_add_observed_var (void *solver, int32_t var) {
  ccadical_add_observed_var ((CCaDiCaL *) solver, var);
}
void ipasir_remove_observed_var (void *solver, int32_t var) {
  ccadical_remove_observed_var ((CCaDiCaL *) solver, var);
}
void ipasir_reset_observed_vars (void *solver) {
  ccadical_reset_observed_vars ((CCaDiCaL *) solver);
}

bool ipasir_is_decision (void *solver, int32_t lit) {
  return ccadical_is_decision ((CCaDiCaL *) solver, lit);
}

void ipasir_phase (void *solver, int32_t lit) {
  ccadical_phase ((CCaDiCaL *) solver, lit);
}
void ipasir_unphase (void *solver, int32_t lit) {
  ccadical_unphase ((CCaDiCaL *) solver, lit);
}

void *ipasir_prop_init (void *state) { return ccadical_prop_init (state); }
void ipasir_prop_release (void *prop) {
  return ccadical_prop_release ((CCaDiCaLPropagator *) prop);
}

void ipasir_prop_lazy (void *prop, bool is_lazy) {
  ccadical_prop_lazy ((CCaDiCaLPropagator *) prop, is_lazy);
}

void ipasir_prop_set_notify_assignment (
    void *prop,
    void (*notify_assignment) (void *state, int32_t lit, bool is_fixed)) {
  ccadical_prop_set_notify_assignment ((CCaDiCaLPropagator *) prop,
                                       notify_assignment);
}
void ipasir_prop_set_notify_new_decision_level (
    void *prop, void (*notify_new_decision_level) (void *state)) {
  ccadical_prop_set_notify_new_decision_level ((CCaDiCaLPropagator *) prop,
                                               notify_new_decision_level);
}
void ipasir_prop_set_notify_backtrack (
    void *prop, void (*notify_backtrack) (void *state, size_t new_level)) {
  ccadical_prop_set_notify_backtrack ((CCaDiCaLPropagator *) prop,
                                      notify_backtrack);
}

void ipasir_prop_set_check_model (
    void *prop,
    bool (*check_model) (void *state, size_t size, const int32_t *model)) {
  ccadical_prop_set_check_model ((CCaDiCaLPropagator *) prop, check_model);
}
void ipasir_prop_set_decide (void *prop, int32_t (*decide) (void *state)) {
  ccadical_prop_set_decide ((CCaDiCaLPropagator *) prop, decide);
}
void ipasir_prop_set_propagate (void *prop,
                                int32_t (*propagate) (void *state)) {
  ccadical_prop_set_propagate ((CCaDiCaLPropagator *) prop, propagate);
}

void ipasir_prop_set_add_reason_clause_lit (
    void *prop,
    int32_t (*add_reason_clause_lit) (void *state, int propagated_lit)) {
  ccadical_prop_set_add_reason_clause_lit ((CCaDiCaLPropagator *) prop,
                                           add_reason_clause_lit);
}

void ipasir_prop_set_has_external_clause (
    void *prop, bool (*has_external_clause) (void *state)) {
  ccadical_prop_set_has_external_clause ((CCaDiCaLPropagator *) prop,
                                         has_external_clause);
}
void ipasir_prop_set_add_external_clause_lit (
    void *prop, int32_t (*add_external_clause_lit) (void *state)) {
  ccadical_prop_set_add_external_clause_lit ((CCaDiCaLPropagator *) prop,
                                             add_external_clause_lit);
}
}
