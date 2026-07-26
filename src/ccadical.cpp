#include "cadical.hpp"
#include "options.hpp"

#include <cstdlib>
#include <cstring>

namespace CaDiCaL {

struct Wrapper : Learner, Terminator, FixedAssignmentListener {

  Solver *solver;
  struct {
    void *state;
    int (*function) (void *);
  } terminator;

  struct {
    void *state;
    void (*function) (void *data, int32_t fixed);
  } fixed_listener;

  struct {
    void *state;
    int max_length;
    int *begin_clause, *end_clause, *capacity_clause;
    void (*function) (void *, int *);
  } learner;

  // ipasir 2 has slightly incompatible types
  struct {
    void *state;
    int max_length;
    int *begin_clause, *end_clause, *capacity_clause;
    void (*function) (void *, int32_t const *, int32_t len,
                      void *proofmeta);
  } learner2;

  bool terminate () {
    if (!terminator.function)
      return false;
    return terminator.function (terminator.state);
  }

  bool learning (int size) {
    if (!learner.function && !learner2.function)
      return false;
    if (learner.function)
      return size <= learner.max_length;
    assert (learner2.function);
    return size <= learner2.max_length;
  }

  void learn (int lit) {
    if (learner.function) {
      if (learner.end_clause == learner.capacity_clause) {
        size_t count = learner.end_clause - learner.begin_clause;
        size_t size = count ? 2 * count : 1;
        learner.begin_clause =
            (int *) realloc (learner.begin_clause, size * sizeof (int));
        learner.end_clause = learner.begin_clause + count;
        learner.capacity_clause = learner.begin_clause + size;
      }
      *learner.end_clause++ = lit;
      if (!lit) {
        learner.function (learner.state, learner.begin_clause);
        learner.end_clause = learner.begin_clause;
      }
    }

    if (learner2.function) {
      if (learner2.end_clause == learner2.capacity_clause) {
        size_t count = learner2.end_clause - learner2.begin_clause;
        size_t size = count ? 2 * count : 1;
        learner2.begin_clause =
            (int *) realloc (learner2.begin_clause, size * sizeof (int));
        learner2.end_clause = learner2.begin_clause + count;
        learner2.capacity_clause = learner2.begin_clause + size;
      }
      *learner2.end_clause++ = lit;
      if (!lit) {
        learner2.function (learner2.state, learner2.begin_clause,
                           learner.end_clause - learner.begin_clause,
                           nullptr);
        learner2.end_clause = learner2.begin_clause;
      }
    }
  }

  void notify_fixed_assignment (int lit) {
    fixed_listener.function (fixed_listener.state, lit);
  }

  Wrapper () : solver (new Solver ()) {
    memset (&terminator, 0, sizeof terminator);
    memset (&learner, 0, sizeof learner);
    memset (&learner2, 0, sizeof learner2);
  }

  ~Wrapper () {
    terminator.function = 0;
    fixed_listener.function = 0;
    if (learner.begin_clause)
      free (learner.begin_clause);
    if (learner2.begin_clause)
      free (learner2.begin_clause);
    delete solver;
  }
};

} // namespace CaDiCaL

using namespace CaDiCaL;

extern "C" {

#include "ccadical.h"

const char *ccadical_signature (void) { return Solver::signature (); }

CCaDiCaL *ccadical_init (void) { return (CCaDiCaL *) new Wrapper (); }

void ccadical_release (CCaDiCaL *wrapper) { delete (Wrapper *) wrapper; }

size_t ccadical_constrain (CCaDiCaL *wrapper, int lit) {
  return ((Wrapper *) wrapper)->solver->constrain (lit);
}

bool ccadical_constraint_failed (CCaDiCaL *wrapper, size_t idx) {
  return ((Wrapper *) wrapper)->solver->constraint_failed (idx);
}

void ccadical_set_option (CCaDiCaL *wrapper, const char *name, int val) {
  ((Wrapper *) wrapper)->solver->set (name, val);
}

COption *ccadical_options (CCaDiCaL *, size_t *len) {
  COption *solver_options = new COption[CaDiCaL::number_of_options];
  // solver_options = (COption *) malloc (CaDiCaL::number_of_options + 1);

  size_t idx = 0;
  for (CaDiCaL::Option *option = CaDiCaL::Options::begin ();
       option != CaDiCaL::Options::end (); ++option) {
    COption &opt = solver_options[idx++];
    opt.name = option->name;
    opt.def = option->def;
    opt.lo = option->lo;
    opt.hi = option->hi;
    // solver_options.push_back (opt);
  }
  *len = CaDiCaL::number_of_options;
  return solver_options;
}

void ccadical_limit (CCaDiCaL *wrapper, const char *name, int val) {
  ((Wrapper *) wrapper)->solver->limit (name, val);
}

int ccadical_get_option (CCaDiCaL *wrapper, const char *name) {
  return ((Wrapper *) wrapper)->solver->get (name);
}

void ccadical_add (CCaDiCaL *wrapper, int lit) {
  ((Wrapper *) wrapper)->solver->add (lit);
}

void ccadical_assume (CCaDiCaL *wrapper, int lit) {
  ((Wrapper *) wrapper)->solver->assume (lit);
}

int ccadical_solve (CCaDiCaL *wrapper) {
  return ((Wrapper *) wrapper)->solver->solve ();
}

int ccadical_simplify (CCaDiCaL *wrapper) {
  return ((Wrapper *) wrapper)->solver->simplify ();
}

int ccadical_val (CCaDiCaL *wrapper, int lit) {
  return ((Wrapper *) wrapper)->solver->val (lit);
}

int ccadical_failed (CCaDiCaL *wrapper, int lit) {
  return ((Wrapper *) wrapper)->solver->failed (lit);
}

void ccadical_print_statistics (CCaDiCaL *wrapper) {
  ((Wrapper *) wrapper)->solver->statistics ();
}

void ccadical_terminate (CCaDiCaL *wrapper) {
  ((Wrapper *) wrapper)->solver->terminate ();
}

int64_t ccadical_active (CCaDiCaL *wrapper) {
  return ((Wrapper *) wrapper)->solver->active ();
}

int64_t ccadical_irredundant (CCaDiCaL *wrapper) {
  return ((Wrapper *) wrapper)->solver->irredundant ();
}

int ccadical_fixed (CCaDiCaL *wrapper, int lit) {
  return ((Wrapper *) wrapper)->solver->fixed (lit);
}

void ccadical_set_terminate (CCaDiCaL *ptr, void *state,
                             int (*terminate) (void *)) {
  Wrapper *wrapper = (Wrapper *) ptr;
  wrapper->terminator.state = state;
  wrapper->terminator.function = terminate;
  if (terminate)
    wrapper->solver->connect_terminator (wrapper);
  else
    wrapper->solver->disconnect_terminator ();
}

void ccadical_set_learn (CCaDiCaL *ptr, void *state, int max_length,
                         void (*learn) (void *state, int *clause)) {
  Wrapper *wrapper = (Wrapper *) ptr;
  wrapper->learner.state = state;
  wrapper->learner.max_length = max_length;
  wrapper->learner.function = learn;
  if (learn)
    wrapper->solver->connect_learner (wrapper);
  else
    wrapper->solver->disconnect_learner ();
}

void ccadical_set_learn2 (CCaDiCaL *ptr, void *state, int max_length,
                          void (*learn) (void *state, int const *clause,
                                         int32_t len, void *proofmeta)) {
  Wrapper *wrapper = (Wrapper *) ptr;
  wrapper->learner2.state = state;
  wrapper->learner2.max_length = max_length;
  wrapper->learner2.function = learn;
  if (learn)
    wrapper->solver->connect_learner (wrapper);
  else
    wrapper->solver->disconnect_learner ();
}

void ccadical_set_fixed_listener (CCaDiCaL *ptr, void *state,
                                  void (*fixed) (void *state, int fixed)) {
  Wrapper *wrapper = (Wrapper *) ptr;
  wrapper->fixed_listener.state = state;
  wrapper->fixed_listener.function = fixed;
  if (fixed)
    wrapper->solver->connect_fixed_listener (wrapper);
  else
    wrapper->solver->disconnect_fixed_listener ();
}

void ccadical_freeze (CCaDiCaL *ptr, int lit) {
  ((Wrapper *) ptr)->solver->freeze (lit);
}

void ccadical_melt (CCaDiCaL *ptr, int lit) {
  ((Wrapper *) ptr)->solver->melt (lit);
}

int ccadical_frozen (CCaDiCaL *ptr, int lit) {
  return ((Wrapper *) ptr)->solver->frozen (lit);
}

int ccadical_trace_proof (CCaDiCaL *ptr, FILE *file, const char *path) {
  return ((Wrapper *) ptr)->solver->trace_proof (file, path);
}

void ccadical_close_proof (CCaDiCaL *ptr) {
  ((Wrapper *) ptr)->solver->close_proof_trace ();
}

void ccadical_conclude (CCaDiCaL *ptr) {
  ((Wrapper *) ptr)->solver->conclude ();
}

int ccadical_vars (CCaDiCaL *ptr) {
  return ((Wrapper *) ptr)->solver->vars ();
}

int ccadical_declare_more_variables (CCaDiCaL *ptr, int number_of_vars) {
  return ((Wrapper *) ptr)->solver->declare_more_variables (number_of_vars);
}

int ccadical_declare_one_more_variable (CCaDiCaL *ptr) {
  return ((Wrapper *) ptr)->solver->declare_one_more_variable ();
}

void ccadical_phase (CCaDiCaL *wrapper, int lit) {
  ((Wrapper *) wrapper)->solver->phase (lit);
}

void ccadical_unphase (CCaDiCaL *wrapper, int lit) {
  ((Wrapper *) wrapper)->solver->unphase (lit);
}
}
