#include "cadical.hpp"
#include "internal.hpp"

#include <cstring>
#include <cstdio>

namespace CaDiCaL {

Solver::Solver () { internal = new Internal (); }
Solver::~Solver () { delete internal; }

#if 0

bool Solver::set (const char * name, const bool val) {
  char * arg = new char [strlen (name) + 15];
  sprintf (arg, "--%s=%s", name, val ? "true" : "false");
  bool res = internal->opts.set (arg);
  delete [] arg;
  return res;
}

bool Solver::set (const char * name, const int val) {
  char * arg = new char [strlen (name) + 15];
  sprintf (arg, "--%s=%d", name, val);
  bool res = internal->opts.set (arg);
  delete [] arg;
  return res;
}

bool Solver::set (const char * name, const double val) {
  char * arg = new char [strlen (name) + 15];
  sprintf (arg, "--%s=%f", name, val);
  bool res = internal->opts.set (arg);
  delete [] arg;
  return res;
}

#endif

bool Solver::set (const char * arg) { return internal->opts.set (arg); }

void Solver::banner () { internal->opts.print (); }
void Solver::options () { internal->opts.print (); }
void Solver::statistics () { internal->stats.print (); }

void Solver::section (const char * title) { SECTION (title); }

void Solver::msg (const char * fmt, ...) {
  va_list ap;
  va_start (ap, fmt);
  Message::print_va_list (internal, 0, fmt, ap);
  va_end (ap);
}

void Solver::die (const char * fmt, ...) {
  va_list ap;
  va_start (ap, fmt);
  Message::die_va_list (internal, fmt, ap);
  va_end (ap);
}

};
