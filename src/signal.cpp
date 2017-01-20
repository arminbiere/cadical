#include "cadical.hpp"
#include "signal.hpp"

/*------------------------------------------------------------------------*/

#include <csignal>

/*------------------------------------------------------------------------*/

extern "C" {
#include <unistd.h>
};

/*------------------------------------------------------------------------*/

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

// TODO printing is not reentrant and might lead to deadlock if the signal
// is raised during another print attempt (and locked IO is used).  To avoid
// this we have to either run our own low-level printing routine here or in
// 'Message' or just dump those statistics somewhere else were we have
// exclusive access to.  All there solutions are painful and not elegant.

void Signal::catchsig (int sig) {
  if (!catchedsig) {
    catchedsig = true;
    solver->message ("");
    solver->message ("CAUGHT SIGNAL %d %s", sig, name (sig));
    solver->section ("result");
    solver->message ("s UNKNOWN");
    solver->statistics ();
  }
  solver->message ("RERAISING SIGNAL %d %s", sig, name (sig));
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
