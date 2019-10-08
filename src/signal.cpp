#include "cadical.hpp"
#include "resources.hpp"
#include "signal.hpp"

/*------------------------------------------------------------------------*/

#include <csignal>
#include <cassert>

/*------------------------------------------------------------------------*/

extern "C" {
#include <unistd.h>
}

/*------------------------------------------------------------------------*/

// Signal handlers for printing statistics even if solver is interrupted.

namespace CaDiCaL {

static volatile bool caught_signal = false;
static volatile bool caught_alarm = false;
static volatile bool alarm_set = false;
static int alarm_time = -1;
static Handler * signal_handler;

void Handler::catch_alarm () { catch_signal (SIGALRM); }

#define SIGNALS \
SIGNAL(SIGABRT) \
SIGNAL(SIGBUS) \
SIGNAL(SIGINT) \
SIGNAL(SIGSEGV) \
SIGNAL(SIGTERM) \

#define SIGNAL(SIG) \
static void (*SIG ## _handler)(int);
SIGNALS
#undef SIGNAL
static void (*SIGALRM_handler)(int);

void Signal::reset_alarm () {
  if (!alarm_set) return;
  (void) signal (SIGALRM, SIGALRM_handler);
  SIGALRM_handler = 0;
  caught_alarm = false;
  alarm_set = false;
  alarm_time = -1;
}

void Signal::reset () {
  signal_handler = 0;
#define SIGNAL(SIG) \
  (void) signal (SIG, SIG ## _handler); \
  SIG ## _handler = 0;
SIGNALS
#undef SIGNAL
  reset_alarm ();
  caught_signal = false;
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
// exclusive access to.  All these solutions are painful and not elegant.

static void catch_signal (int sig) {
  if (sig == SIGALRM && absolute_real_time () >= alarm_time) {
    if (!caught_alarm) {
      caught_alarm = true;
      if (signal_handler) signal_handler->catch_alarm ();
    }
    Signal::reset_alarm ();
  } else {
    if (!caught_signal) {
      caught_signal = true;
      if (signal_handler) signal_handler->catch_signal (sig);
    }
    Signal::reset ();
    ::raise (sig);
  }
}

void Signal::set (Handler * h) {
  signal_handler = h;
#define SIGNAL(SIG) \
  SIG ## _handler = signal (SIG, catch_signal);
SIGNALS
#undef SIGNAL
}

void Signal::alarm (int seconds) {
  assert (seconds >= 0);
  assert (!alarm_set);
  assert (alarm_time < 0);
  SIGALRM_handler = signal (SIGALRM, catch_signal);
  alarm_set = true;
  alarm_time = absolute_real_time () + seconds;
  ::alarm (seconds);
}

}
