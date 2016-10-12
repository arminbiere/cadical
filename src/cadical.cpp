#include "cadical.hpp"
#include "internal.hpp"
#include "../build/config.hpp"

#include <cstring>
#include <cstdio>

namespace CaDiCaL {

Solver::Solver () { internal = new Internal (); }
Solver::~Solver () { delete internal; }

int Solver::max () const { return internal->max_var; }

/*------------------------------------------------------------------------*/

bool Solver::has (const char * arg) { return internal->opts.has (arg); }

double Solver::get (const char * arg) { return internal->opts.get (arg); }

bool Solver::set (const char * arg, double val) {
  return internal->opts.set (arg, val);
}

bool Solver::set (const char * arg) { return internal->opts.set (arg); }

/*------------------------------------------------------------------------*/

int Solver::val (int lit) { return internal->val (lit); }
int Solver::solve () { return internal->solve (); }

/*------------------------------------------------------------------------*/

void Solver::close () {
  if (!internal->proof) return;
  delete internal->proof;
  internal->proof = 0;
}

void Solver::proof (FILE * external_file, const char * name) {
  File * internal_file = File::write (external_file, name);
  assert (internal_file);
  close ();
  internal->proof =
    new Proof (internal, internal_file, internal->opts.binary);
}

bool Solver::proof (const char * path) {
  File * internal_file = File::write (path);
  if (!internal_file) return false;
  close ();
  internal->proof =
    new Proof (internal, internal_file, internal->opts.binary);
  return true;
}

/*------------------------------------------------------------------------*/

void Solver::banner () {
  section ("banner");
  msg ("CaDiCaL Radically Simplified CDCL SAT Internal");
  msg ("Version " CADICAL_VERSION " " CADICAL_GITID);
  msg ("Copyright (c) 2016 Armin Biere, JKU");
  msg (CADICAL_CXXVERSION);
  msg (CADICAL_COMPILED);
  msg (CADICAL_OS);
  msg (CADICAL_CXX CADICAL_CXXFLAGS);
}

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
