#include "cadical.hpp"
#include "signal.hpp"

#include <csignal>

extern "C" {
#include <unistd.h>
};

// Signal handlers for printing statistics even if solver is interrupted.

namespace CaDiCaL {

bool Signal::catchedsig = false;
Solver * Signal::solver;

#define SIGNALS \
SIGNAL(SIGINT) \
SIGNAL(SIGSEGV) \
SIGNAL(SIGABRT) \
SIGNAL(SIGTERM) \
SIGNAL(SIGBUS) \

#define SIGNAL(SIG) \
static void (*SIG ## _handler)(int);
SIGNALS
#undef SIGNAL

void Signal::reset () {
#define SIGNAL(SIG) \
  (void) signal (SIG, SIG ## _handler);
SIGNALS
#undef SIGNAL
  solver = 0;
  catchedsig = 0;
}

const char * Signal::name (int sig) {
#define SIGNAL(SIG) \
  if (sig == SIG) return # SIG; else
  SIGNALS
#undef SIGNAL
  return "UNKNOWN";
}

void Signal::catchsig (int sig) {
  if (!catchedsig) {
    catchedsig = true;
    solver->msg ("");
    solver->msg ("CAUGHT SIGNAL %d %s", sig, name (sig));
    solver->section ("result");
    solver->msg ("s UNKNOWN");
    solver->statistics ();
  }
  solver->msg ("RERAISING SIGNAL %d %s", sig, name (sig));
  reset ();
  raise (sig);
}

void Signal::init (Solver * s) {
#define SIGNAL(SIG) \
  SIG ## _handler = signal (SIG, Signal::catchsig);
SIGNALS
#undef SIGNAL
  solver = s;
}

};
