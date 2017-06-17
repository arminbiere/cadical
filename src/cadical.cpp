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
  INITIALIZED ();
  delete external;
  delete internal;
}

/*------------------------------------------------------------------------*/

int Solver::max () const {
  INITIALIZED ();
  return external->max_var;
}

void Solver::init (int new_max) {
  INITIALIZED ();
  external->init (new_max);
}

/*------------------------------------------------------------------------*/

bool Solver::has (const char * arg) {
  INITIALIZED ();
  return internal->opts.has (arg);
}

double Solver::get (const char * arg) {
  INITIALIZED ();
  return internal->opts.get (arg);
}

bool Solver::set (const char * arg, double val) {
  INITIALIZED ();
  return internal->opts.set (arg, val);
}

bool Solver::set (const char * arg) {
  INITIALIZED ();
  return internal->opts.set (arg);
}

/*------------------------------------------------------------------------*/

void Solver::add (int lit) {
  INITIALIZED ();
  external->add (lit);
}

int Solver::val (int lit) {
  INITIALIZED ();
  return external->val (lit);
}

int Solver::solve () {
  INITIALIZED ();
  return external->solve ();
}

/*------------------------------------------------------------------------*/

void Solver::close () {
  INITIALIZED ();
  if (!internal->proof) return;
  section ("closing proof");
  internal->close_proof ();
}

void Solver::proof (FILE * external_file, const char * name) {
  INITIALIZED ();
  File * internal_file = File::write (internal, external_file, name);
  assert (internal_file);
  internal->new_proof (internal_file, true);
}

bool Solver::proof (const char * path) {
  INITIALIZED ();
  File * internal_file = File::write (internal, path);
  if (!internal_file) return false;
  internal->new_proof (internal_file, true);
  return true;
}

/*------------------------------------------------------------------------*/

void Solver::banner () {
  INITIALIZED ();
  message ("CaDiCaL Radically Simplified CDCL SAT Solver");
  message ("Version " CADICAL_VERSION " " CADICAL_GITID);
  message ("Copyright (c) 2016-2017 Armin Biere, JKU");
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
  INITIALIZED ();
  internal->opts.print ();
}

void Solver::usage () {
  INITIALIZED ();
  internal->opts.usage ();
}

void Solver::statistics () {
  INITIALIZED ();
  internal->stats.print (internal);
}

/*------------------------------------------------------------------------*/

const char * Solver::dimacs (File * file) {
  INITIALIZED ();
  Parser * parser = new Parser (internal, external, file);
  const char * err = parser->parse_dimacs ();
  delete parser;
  return err;
}

const char * Solver::dimacs (FILE * external_file, const char * name) {
  INITIALIZED ();
  File * file = File::read (internal, external_file, name);
  assert (file);
  const char * err = dimacs (file);
  delete file;
  return err;
}

const char * Solver::dimacs (const char * path) {
  INITIALIZED ();
  File * file = File::read (internal, path);
  if (!file)
    return internal->error.init ("failed to read DIMACS file '%s'", path);
  const char * err = dimacs (file);
  delete file;
  return err;
}

File * Solver::output () {
  INITIALIZED ();
  return internal->output;
}

const char * Solver::solution (const char * path) {
  INITIALIZED ();
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
  INITIALIZED ();
  SECTION (title);
}

void Solver::message (const char * fmt, ...) {
  INITIALIZED ();
#ifndef QUIET
  va_list ap;
  va_start (ap, fmt);
  Message::vmessage (internal, fmt, ap);
  va_end (ap);
#endif
}

void Solver::error (const char * fmt, ...) {
  INITIALIZED ();
  va_list ap;
  va_start (ap, fmt);
  Message::verror (internal, fmt, ap);
  va_end (ap);
}

};
