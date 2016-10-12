#include "cadical.hpp"
#include "internal.hpp"

#include <cstring>
#include <cstdio>

namespace CaDiCaL {

Solver::Solver () { internal = new Internal (); }
Solver::~Solver () { delete internal; }

/*------------------------------------------------------------------------*/

bool Solver::has (const char * arg) { return internal->opts.has (arg); }

double Solver::get (const char * arg) { return internal->opts.get (arg); }

bool Solver::set (const char * arg, double val) {
  return internal->opts.set (arg, val);
}

bool Solver::set (const char * arg) { return internal->opts.set (arg); }

/*------------------------------------------------------------------------*/

void Solver::banner () { internal->opts.print (); }
void Solver::options () { internal->opts.print (); }
void Solver::statistics () { internal->stats.print (); }

/*------------------------------------------------------------------------*/

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
