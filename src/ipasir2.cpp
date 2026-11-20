#include "ipasir2.h"
#include "ccadical.h"

#include "options.hpp"

#include <vector>

extern "C" {

ipasir2_errorcode ipasir2_signature (char const **signature) {
  *signature = ccadical_signature ();
  return IPASIR2_E_OK;
}

ipasir2_errorcode ipasir2_init (void **solver) {
  CCaDiCaL *cadical = ccadical_init ();
  *solver = cadical;
  ccadical_set_option (cadical, "factor", 0);
  return IPASIR2_E_OK;
}

ipasir2_errorcode ipasir2_release (void *solver) {
  ccadical_release ((CCaDiCaL *) solver);
  return IPASIR2_E_OK;
}

IPASIR_API ipasir2_errorcode
ipasir2_options (void *solver, ipasir2_option const **options, int *count) {
  size_t len;
  COption *option_defs = ccadical_options ((CCaDiCaL *) solver, &len);
  *count = (int) len;
  int n_extra = 2;

  std::vector<ipasir2_option> extra;
  extra.resize (n_extra);

  std::vector<ipasir2_option> solver_options;
  solver_options.resize (CaDiCaL::number_of_options + n_extra + 1);

  int i = 0;
  for (; i < n_extra; ++i) {
    solver_options[i] = extra[i];
  }

  for (COption *option = option_defs; option != option_defs + *count;
       ++option) {
    solver_options[i].name = option->name;
    solver_options[i].min = option->lo;
    solver_options[i].max = option->hi;
    if (strcmp (option->name, "log") && strcmp (option->name, "quiet") &&
        strcmp (option->name, "report") &&
        strcmp (option->name, "verbose")) {
      solver_options[i].max_state = IPASIR2_S_CONFIG;
    } else
      solver_options[i].max_state = IPASIR2_S_SOLVING;
    solver_options[i].tunable = true;
    solver_options[i].indexed = 0;
    solver_options[i].handle =
        (void const *) +[] (CCaDiCaL *solver, ipasir2_option const *opt,
                            int64_t value) {
          ccadical_set_option (solver, opt->name, value);
        };
    ++i;
  }
  *options = solver_options.data ();
  return IPASIR2_E_OK;
}

ipasir2_errorcode ipasir2_set_option (void *solver,
                                      ipasir2_option const *handle,
                                      int64_t value, int64_t) {
  ccadical_set_option ((CCaDiCaL *) solver, handle->name, value);
  return IPASIR2_E_OK;
}

IPASIR_API ipasir2_errorcode ipasir2_add (void *solver,
                                          int32_t const *clause,
                                          int32_t len, int32_t, void *) {
  for (auto it = clause; it != clause + len; ++it)
    ccadical_add ((CCaDiCaL *) solver, *it);
  ccadical_add ((CCaDiCaL *) solver, 0);
  return IPASIR2_E_OK;
}

ipasir2_errorcode ipasir2_solve (void *solver, int *result,
                                 int32_t const *literals, int32_t len) {
  for (auto it = literals; it != literals + len; ++it)
    ccadical_assume ((CCaDiCaL *) solver, *it);
  *result = ccadical_solve ((CCaDiCaL *) solver);
  return IPASIR2_E_OK;
}

ipasir2_errorcode ipasir2_val (void *solver, int32_t lit, int32_t *result) {
  *result = ccadical_val ((CCaDiCaL *) solver, lit);
  return IPASIR2_E_OK;
}

ipasir2_errorcode ipasir2_failed (void *solver, int32_t lit, int *result) {
  *result = ccadical_failed ((CCaDiCaL *) solver, lit);
  return IPASIR2_E_OK;
}
ipasir2_errorcode ipasir2_set_terminate (void *solver, void *data,
                                         int (*callback) (void *data)) {
  ccadical_set_terminate ((CCaDiCaL *) solver, data, callback);
  return IPASIR2_E_OK;
}

IPASIR_API ipasir2_errorcode
ipasir2_set_export (void *solver, void *state, int max_length,
                    void (*learn) (void *data, int32_t const *clause,
                                   int32_t len, void *proofmeta)) {
  ccadical_set_learn2 ((CCaDiCaL *) solver, state, max_length, learn);
  return IPASIR2_E_OK;
}

IPASIR_API ipasir2_errorcode ipasir2_set_import (void *, void *,
                                                 void (*) (void *data)) {
  return IPASIR2_E_UNSUPPORTED;
}

ipasir2_errorcode ipasir2_set_fixed (void *solver, void *state,
                                     void (*callback) (void *data,
                                                       int32_t fixed)) {
  ccadical_set_fixed_listener ((CCaDiCaL *) solver, state, callback);
  return IPASIR2_E_OK;
}
}
