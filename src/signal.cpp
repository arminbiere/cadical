
#include "cadical.hpp"

#include <csignal>

// Signal handlers for printing statistics even if solver is interrupted.

namespace CaDiCaL {

static bool catchedsig = false;
static Solver * global_solver;

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

void reset_signal_handlers (void) {
#define SIGNAL(SIG) \
  (void) signal (SIG, SIG ## _handler);
SIGNALS
#undef SIGNAL
}

static const char * signal_name (int sig) {
#define SIGNAL(SIG) \
  if (sig == SIG) return # SIG; else
  SIGNALS
#undef SIGNAL
  return "UNKNOWN";
}

static void catchsig (int sig) {
  Solver & solver = *global_solver;
  if (!catchedsig) {
    catchedsig = true;
    MSG ("");
    MSG ("CAUGHT SIGNAL %d %s", sig, signal_name (sig));
    SECTION ("result");
    MSG ("s UNKNOWN");
    solver.stats.print ();
  }
  reset_signal_handlers ();
  MSG ("RERAISING SIGNAL %d %s", sig, signal_name (sig));
  raise (sig);
}

static void init_signal_handlers (Solver & s) {
#define SIGNAL(SIG) \
  SIG ## _handler = signal (SIG, catchsig);
SIGNALS
#undef SIGNAL
  global_solver_ptr = &s;
}


};
