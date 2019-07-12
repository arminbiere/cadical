#include "cadical.hpp"

namespace CaDiCaL {

struct Wrapper : Terminator {
  Solver * solver;
  void * state;
  int (*function) (void *);
  bool terminate () { return function ? function (state) : false; }
  Wrapper () : solver (new Solver ()), state (0), function (0) { }
  ~Wrapper () { function = 0; delete solver; }
};

}

using namespace CaDiCaL;

extern "C" {

#include "ccadical.h"

const char * ccadical_signature (void) {
  return Solver::signature ();
}

CCaDiCaL * ccadical_init (void) {
  return (CCaDiCaL*) new Wrapper ();
}

void ccadical_release (CCaDiCaL * wrapper) {
  delete (Wrapper*) wrapper;
}

void ccadical_set_option (CCaDiCaL * wrapper,
                          const char * name, int val) {
  ((Wrapper*) wrapper)->solver->set (name, val);
}

void ccadical_limit (CCaDiCaL * wrapper,
                     const char * name, int val) {
  ((Wrapper*) wrapper)->solver->limit (name, val);
}

int ccadical_get_option (CCaDiCaL * wrapper, const char * name) {
  return ((Wrapper*) wrapper)->solver->get (name);
}

void ccadical_add (CCaDiCaL * wrapper, int lit) {
  ((Wrapper*) wrapper)->solver->add (lit);
}

void ccadical_assume (CCaDiCaL * wrapper, int lit) {
  ((Wrapper*) wrapper)->solver->assume (lit);
}

int ccadical_solve (CCaDiCaL * wrapper) {
  return ((Wrapper*) wrapper)->solver->solve ();
}

int ccadical_simplify (CCaDiCaL * wrapper) {
  return ((Wrapper*) wrapper)->solver->simplify ();
}

int ccadical_val (CCaDiCaL * wrapper, int lit) {
  return ((Wrapper*) wrapper)->solver->val (lit);
}

int ccadical_failed (CCaDiCaL * wrapper, int lit) {
  return ((Wrapper*) wrapper)->solver->failed (lit);
}

void ccadical_print_statistics (CCaDiCaL * wrapper) {
  ((Wrapper*) wrapper)->solver->statistics ();
}

void ccadical_terminate (CCaDiCaL * wrapper) {
  ((Wrapper*) wrapper)->solver->terminate ();
}

int64_t ccadical_active (CCaDiCaL * wrapper) {
  return ((Wrapper*) wrapper)->solver->active ();
}

int64_t ccadical_irredundant (CCaDiCaL * wrapper) {
  return ((Wrapper*) wrapper)->solver->irredundant ();
}

int ccadical_fixed (CCaDiCaL * wrapper, int lit) {
  return ((Wrapper*) wrapper)->solver->fixed (lit);
}

void ccadical_set_terminate (CCaDiCaL * ptr,
                             void * state, int (*terminate)(void *)) {
  Wrapper * wrapper = (Wrapper *) ptr;
  wrapper->state = state;
  wrapper->function = terminate;
  if (terminate) wrapper->solver->connect_terminator (wrapper);
  else wrapper->solver->disconnect_terminator ();
}

void ccadical_freeze (CCaDiCaL * ptr, int lit) {
  ((Wrapper*) ptr)->solver->freeze (lit);
}

void ccadical_melt (CCaDiCaL * ptr, int lit) {
  ((Wrapper*) ptr)->solver->melt (lit);
}

int ccadical_frozen (CCaDiCaL * ptr, int lit) {
  return ((Wrapper*) ptr)->solver->frozen (lit);
}

}
