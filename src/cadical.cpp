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

int Solver::solve () { 
  int res = internal->solve ();
  if (res == 10) internal->check (&Internal::val);
  return res;
}

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

const char * Solver::dimacs (const char * path) {
  File * file = File::read (path);
  if (!file)
    return internal->error.init ("failed to read DIMACS file '%s'", path);
  section ("parsing input");
  Parser * parser = new Parser (internal, file);
  msg ("reading DIMACS file from '%s'", file->name ());
  const char * err = parser->parse_dimacs ();
  delete parser;
  delete file;
  return err;
}

const char * Solver::solution (const char * path) {
  File * file = File::read (path);
  if (!file)
    return internal->error.init ("failed to read solution file '%s'", path);
  section ("parsing solution");
  Parser * parser = new Parser (internal, file);
  msg ("reading solution file from '%s'", file->name ());
  const char * err = parser->parse_solution ();
  delete parser;
  delete file;
  if (!err) internal->check (&Internal::sol);
  return err;
}

/*------------------------------------------------------------------------*/

void Solver::section (const char * title) { SECTION (title); }

void Solver::msg (const char * fmt, ...) {
  va_list ap;
  va_start (ap, fmt);
  Message::print_va_list (internal, 0, fmt, ap);
  va_end (ap);
}

void Solver::err (const char * fmt, ...) {
  va_list ap;
  va_start (ap, fmt);
  Message::err_va_list (internal, fmt, ap);
  va_end (ap);
}

};
