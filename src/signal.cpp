#include "cadical.hpp"
#include "signal.hpp"

/*------------------------------------------------------------------------*/

#include <csignal>
#include <cassert>

int CaDiCaL::Solver::contract_violation_signal = SIGUSR1;

/*------------------------------------------------------------------------*/

extern "C" {
#include <unistd.h>
};

/*------------------------------------------------------------------------*/

// Signal handlers for printing statistics even if solver is interrupted.

namespace CaDiCaL {

bool Signal::catchedsig = false;
bool Signal::alarmset = false;
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
static void (*SIGALRM_handler)(int);

void Signal::reset () {
#define SIGNAL(SIG) \
  (void) signal (SIG, SIG ## _handler); \
  SIG ## _handler = 0;
SIGNALS
#undef SIGNAL
  if (alarmset)
    (void) signal (SIGALRM, SIGALRM_handler),
    SIGALRM_handler = 0,
    alarmset = false;
  solver = 0;
  catchedsig = 0;
}

const char * Signal::name (int sig) {
#define SIGNAL(SIG) \
  if (sig == SIG) return # SIG;
  SIGNALS
#undef SIGNAL
  if (sig == SIGALRM) return "SIGALRM";
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

void Signal::alarm (int seconds) {
  assert (!alarmset);
  SIGALRM_handler = signal (SIGALRM, Signal::catchsig);
  alarmset = true;
  ::alarm (seconds);
}

};
