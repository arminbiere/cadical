#include "internal.hpp"

/*------------------------------------------------------------------------*/

#include <config.hpp>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// See header file 'cadical.hpp' for more information.

/*------------------------------------------------------------------------*/

Solver::Solver () {
  internal = new Internal ();
  external = new External (internal);
}

Solver::~Solver () {
  REQUIRE_INITIALIZED ();
  delete external;
  delete internal;
}

/*------------------------------------------------------------------------*/

int Solver::max () const {
  REQUIRE_INITIALIZED ();
  return external->max_var;
}

void Solver::init (int new_max) {
  REQUIRE_INITIALIZED ();
  external->init (new_max);
}

/*------------------------------------------------------------------------*/

bool Solver::has (const char * arg) {
  REQUIRE_INITIALIZED ();
  return internal->opts.has (arg);
}

double Solver::get (const char * arg) {
  REQUIRE_INITIALIZED ();
  return internal->opts.get (arg);
}

bool Solver::set (const char * arg, double val) {
  REQUIRE_INITIALIZED ();
  return internal->opts.set (arg, val);
}

bool Solver::set (const char * arg) {
  REQUIRE_INITIALIZED ();
  return internal->opts.set (arg);
}

/*------------------------------------------------------------------------*/

void Solver::add (int lit) {
  REQUIRE_INITIALIZED ();
  REQUIRE_VALID_LIT (lit);
  external->add (lit);
}

int Solver::val (int lit) {
  REQUIRE_INITIALIZED ();
  REQUIRE_VALID_LIT (lit);
  return external->val (lit);
}

int Solver::solve () {
  REQUIRE_INITIALIZED ();
  return external->solve ();
}

/*------------------------------------------------------------------------*/

void Solver::terminate () { external->terminate (); }

/*------------------------------------------------------------------------*/

void Solver::close () {
  REQUIRE_INITIALIZED ();
  if (!internal->proof) return;
  section ("closing proof");
  internal->close_proof ();
}

void Solver::proof (FILE * external_file, const char * name) {
  REQUIRE_INITIALIZED ();
  File * internal_file = File::write (internal, external_file, name);
  assert (internal_file);
  internal->new_proof (internal_file, true);
}

bool Solver::proof (const char * path) {
  REQUIRE_INITIALIZED ();
  File * internal_file = File::write (internal, path);
  if (!internal_file) return false;
  internal->new_proof (internal_file, true);
  return true;
}

/*------------------------------------------------------------------------*/

void Solver::banner () {
  REQUIRE_INITIALIZED ();
  message ("CaDiCaL Radically Simplified CDCL SAT Solver");
  message ("Version " CADICAL_VERSION " " CADICAL_GITID);
  message ("Copyright (c) 2016-2018 Armin Biere, JKU");
  message ("");
  message (CADICAL_COMPILED);
  message (CADICAL_CXXVERSION);
  message (CADICAL_OS);
  message (CADICAL_CXX " " CADICAL_CXXFLAGS);
}

const char * Solver::version () {
  return CADICAL_VERSION;
}

void Solver::options () {
  REQUIRE_INITIALIZED ();
  internal->opts.print ();
}

void Solver::usage () {
  REQUIRE_INITIALIZED ();
  internal->opts.usage ();
}

void Solver::statistics () {
  REQUIRE_INITIALIZED ();
  internal->stats.print (internal);
}

/*------------------------------------------------------------------------*/

const char * Solver::dimacs (File * file) {
  REQUIRE_INITIALIZED ();
  Parser * parser = new Parser (internal, external, file);
  const char * err = parser->parse_dimacs ();
  delete parser;
  return err;
}

const char * Solver::dimacs (FILE * external_file, const char * name) {
  REQUIRE_INITIALIZED ();
  File * file = File::read (internal, external_file, name);
  assert (file);
  const char * err = dimacs (file);
  delete file;
  return err;
}

const char * Solver::dimacs (const char * path) {
  REQUIRE_INITIALIZED ();
  File * file = File::read (internal, path);
  if (!file)
    return internal->error.init ("failed to read DIMACS file '%s'", path);
  const char * err = dimacs (file);
  delete file;
  return err;
}

File * Solver::output () {
  REQUIRE_INITIALIZED ();
  return internal->output;
}

const char * Solver::solution (const char * path) {
  REQUIRE_INITIALIZED ();
  File * file = File::read (internal, path);
  if (!file)
    return internal->error.init ("failed to read solution file '%s'", path);
  Parser * parser = new Parser (internal, external, file);
  const char * err = parser->parse_solution ();
  delete parser;
  delete file;
  if (!err) external->check (&External::sol);
  return err;
}

/*------------------------------------------------------------------------*/

void Solver::section (const char * title) {
  REQUIRE_INITIALIZED ();
  SECTION (title);
}

void Solver::message (const char * fmt, ...) {
  REQUIRE_INITIALIZED ();
#ifndef QUIET
  va_list ap;
  va_start (ap, fmt);
  Message::vmessage (internal, fmt, ap);
  va_end (ap);
#endif
}

void Solver::error (const char * fmt, ...) {
  REQUIRE_INITIALIZED ();
  va_list ap;
  va_start (ap, fmt);
  Message::verror (internal, fmt, ap);
  va_end (ap);
}

};
