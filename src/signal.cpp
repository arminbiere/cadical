#include "signal.hpp"
#include "cadical.hpp"
#include "resources.hpp"

/*------------------------------------------------------------------------*/

#include <cassert>
#include <csignal>

/*------------------------------------------------------------------------*/

extern "C" {
#include <unistd.h>
}

/*------------------------------------------------------------------------*/

// Signal handlers for printing statistics even if solver is interrupted.

namespace CaDiCaL {

static volatile sig_atomic_t signal_value = 0;
static volatile bool caught_signal = false;
static Handler *signal_handler;

#ifndef _WIN32

static volatile bool caught_alarm = false;
static volatile bool alarm_set = false;
static int alarm_time = -1;

void Handler::catch_alarm () { catch_signal (SIGALRM); }

#endif

#define SIGNALS \
  SIGNAL (SIGABRT) \
  SIGNAL (SIGINT) \
  SIGNAL (SIGSEGV) \
  SIGNAL (SIGTERM)

#define SIGNAL(SIG) static void (*SIG##_handler) (int);
SIGNALS
#undef SIGNAL

#ifndef _WIN32

static void (*SIGALRM_handler) (int);

void Signal::reset_alarm () {
  if (!alarm_set)
    return;
  (void) signal (SIGALRM, SIGALRM_handler);
  SIGALRM_handler = 0;
  caught_alarm = false;
  alarm_set = false;
  alarm_time = -1;
}

#endif

void Signal::reset () {
  signal_handler = 0;
#define SIGNAL(SIG) \
  (void) signal (SIG, SIG##_handler); \
  SIG##_handler = 0;
  SIGNALS
#undef SIGNAL
#ifndef _WIN32
  reset_alarm ();
#endif
  caught_signal = false;
  signal_value = 0;
}

const char *Signal::name (int sig) {
#define SIGNAL(SIG) \
  if (sig == SIG) \
    return #SIG;
  SIGNALS
#undef SIGNAL
#ifndef _WIN32
  if (sig == SIGALRM)
    return "SIGALRM";
#endif
  return "UNKNOWN";
}

static void catch_signal (int sig) {
#ifndef _WIN32
  if (sig == SIGALRM && absolute_real_time () >= alarm_time) {
    if (!caught_alarm) {
      caught_alarm = true;
      if (signal_handler)
        signal_handler->catch_alarm ();
    }
    Signal::reset_alarm ();
  } else
#endif
  {
    // Reraising should happen in solver control for SIGINT and SIGTERM.
    // For SIGABRT and SIGSEGV we reraise immediately.
    switch (sig) {
    case SIGABRT:
    case SIGSEGV:
      Signal::reset ();
      ::raise (sig);
    default:
      break;
    }
    if (!caught_signal) {
      caught_signal = true;
      if (signal_handler)
        signal_handler->catch_signal (sig);
    }
  }
}

void Signal::set (Handler *h) {
  signal_handler = h;
#define SIGNAL(SIG) SIG##_handler = signal (SIG, catch_signal);
  SIGNALS
#undef SIGNAL
}

#ifndef _WIN32

void Signal::alarm (int seconds) {
  assert (seconds >= 0);
  assert (!alarm_set);
  assert (alarm_time < 0);
  SIGALRM_handler = signal (SIGALRM, catch_signal);
  alarm_set = true;
  alarm_time = absolute_real_time () + seconds;
  ::alarm (seconds);
}

#endif

void Signal::set_received (int sig) { signal_value = sig; }

int Signal::received () { return signal_value; }

// Signals for which returning control is sensible
bool Signal::interrupted () {
  const int sig = received ();
  return sig == SIGINT || sig == SIGTERM;
}

} // namespace CaDiCaL
