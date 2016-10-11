#include "cadical.hpp"
#include "internal.hpp"

namespace CaDiCaL {

Solver::Solver () { internal = new Internal (); }
Solver::~Solver () { delete internal; }

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
