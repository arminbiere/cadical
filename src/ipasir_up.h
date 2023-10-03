#ifndef _ipasir_up_h_INCLUDED
#define _ipasir_up_h_INCLUDED

#include <stddef.h>
#include <stdint.h>

/*------------------------------------------------------------------------*/
#ifdef __cplusplus
extern "C" {
#endif
/*------------------------------------------------------------------------*/

// Add call-back which allows to learn, propagate and backtrack based on
// external constraints. Only one external propagator can be connected
// and after connection every related variables must be 'observed' (use
// 'add_observed_var' function).
// Disconnection of the external propagator resets all the observed
// variables.
//
//   require (VALID)
//   ensure (VALID)
//
void ipasir_connect_external_propagator (void *solver, void *propagator);
void ipasir_disconnect_external_propagator (void *solver);

// Mark as 'observed' those variables that are relevant to the external
// propagator. External propagation, clause addition during search and
// notifications are all over these observed variabes.
// A variable can not be observed witouth having an external propagator
// connected. Observed variables are "frozen" internally, and so
// inprocessing will not consider them as candidates for elimination.
// An observed variable is allowed to be a fresh variable and it can be
// added also during solving.
//
//   require (VALID_OR_SOLVING)
//   ensure (VALID_OR_SOLVING)
//
void ipasir_add_observed_var (void *solver, int32_t var);

// Removes the 'observed' flag from the given variable. A variable can be
// set unobserved only between solve calls, not during it (to guarantee
// that no yet unexplained external propagation involves it).
//
//   require (VALID)
//   ensure (VALID)
//
void ipasir_remove_observed_var (void *solver, int32_t var);

// Removes all the 'observed' flags from the variables. Disconnecting the
// propagator invokes this step as well.
//
//   require (VALID)
//   ensure (VALID)
//
void ipasir_reset_observed_vars (void *solver);

// Get reason of valid observed literal (true = it is an observed variable
// and it got assigned by a decision during the CDCL loop. Otherwise:
// false.
//
//   require (VALID_OR_SOLVING)
//   ensure (VALID_OR_SOLVING)
//
bool ipasir_is_decision (void *solver, int32_t lit);

void ipasir_phase (void *solver, int32_t lit);
void ipasir_unphase (void *solver, int32_t lit);

void *ipasir_prop_init (void *state);
void ipasir_prop_release (void *prop);

// This flag is currently checked only when the propagator is connected.
// lazy propagator only checks complete assignments
void ipasir_prop_lazy (void *prop, bool is_lazy);

// Notify the propagator about assignments to observed variables.
// The notification is not necessarily eager. It usually happens before
// the call of propagator callbacks and when a driving clause is leading
// to an assignment.
void ipasir_prop_set_notify_assignment (
    void *prop,
    void (*notify_assignment) (void *state, int32_t lit, bool is_fixed));
void ipasir_prop_set_notify_new_decision_level (
    void *prop, void (*notify_new_decision_level) (void *state));
void ipasir_prop_set_notify_backtrack (
    void *prop, void (*notify_backtrack) (void *state, size_t new_level));

// Check by the external propagator the found complete solution (after
// solution reconstruction). If it returns false, the propagator must
// provide an external clause during the next callback.
void ipasir_prop_set_check_model (
    void *prop,
    bool (*check_model) (void *state, size_t size, const int32_t *model));

// Ask the external propagator for the next decision literal. If it
// returns 0, the solver makes its own choice.
void ipasir_prop_set_decide (void *prop, int32_t (*decide) (void *state));

// Ask the external propagator if there is an external propagation to make
// under the current assignment. It returns either a literal to be
// propagated or 0, indicating that there is no external propagation under
// the current assignment.
void ipasir_prop_set_propagate (void *prop,
                                int32_t (*propagate) (void *state));

// Ask the external propagator for the reason clause of a previous
// external propagation step (done by cb_propagate). The clause must be
// added literal-by-literal closed with a 0. Further, the clause must
// contain the propagated literal.
void ipasir_prop_set_add_reason_clause_lit (
    void *prop,
    int32_t (*add_reason_clause_lit) (void *state, int propagated_lit));

// The following two functions are used to add external clauses to the
// solver during the CDCL loop. The external clause is added
// literal-by-literal and learned by the solver as an irredundant
// (original) input clause. The clause can be arbitrary, but if it is
// root-satisfied or tautology, the solver will ignore it without learning
// it. Root-falsified literals are eagerly removed from the clause.
// Falsified clauses trigger conflict analysis, propagating clauses
// trigger propagation. In case chrono is 0, the solver backtracks to
// propagate the new literal on the right decision level, otherwise it
// potentially will be an out-of-order assignment on the current level.
// Unit clauses always (unless root-satisfied, see above) trigger
// backtracking (independently from the value of the chrono option and
// independently from being falsified or satisfied or unassigned) to level
// 0. Empty clause (or root falsified clause, see above) makes the problem
// unsat and stops the search immediately. A literal 0 must close the
// clause.

// The external propagator indicates that there is a clause to add.
void ipasir_prop_set_has_external_clause (
    void *prop, bool (*has_external_clause) (void *state));

// The actual function called to add the external clause.
void ipasir_prop_set_add_external_clause_lit (
    void *prop, int32_t (*add_external_clause_lit) (void *state));

/*------------------------------------------------------------------------*/
#ifdef __cplusplus
}
#endif
/*------------------------------------------------------------------------*/

#endif
