#include "parse.hpp"
#include "solver.hpp"
#include "file.hpp"
#include "logging.hpp"

#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <cctype>
#include <climits>

namespace CaDiCaL {

int Parser::parse_char () { return file->get (); }

void Parser::parse_string (const char * str, char prev) {
  for (const char * p = str; *p; p++)
    if (parse_char () == *p) prev = *p;
    else PER ("expected '%c' after '%c'", *p, prev);
}

int Parser::parse_positive_int (int ch, int & res, const char * name) {
  assert (isdigit (ch));
  res = ch - '0';
  while (isdigit (ch = parse_char ())) {
    int digit = ch - '0';
    if (INT_MAX/10 < res || INT_MAX - digit < 10*res)
      PER ("too large '%s' in header", name);
    res = 10*res + digit;
  }
  return ch;
}

int Parser::parse_lit (int ch, int & lit) {
  int sign = 0;
  if (ch == '-') {
    if (!isdigit (ch = parse_char ())) PER ("expected digit after '-'");
    sign = -1;
  } else if (!isdigit (ch)) PER ("expected digit or '-'");
  else sign = 1;
  lit = ch - '0';
  while (isdigit (ch = parse_char ())) {
    int digit = ch - '0';
    if (INT_MAX/10 < lit || INT_MAX - digit < 10*lit)
      PER ("literal too large");
    lit = 10*lit + digit;
  }
  if (ch == '\r') ch = parse_char ();
  if (ch != 'c' && ch != ' ' && ch != '\t' && ch != '\n')
    PER ("expected white space after '%d'", sign*lit);
  if (lit > solver->max_var)
    PER ("literal %d exceeds maximum variable %d", sign*lit, solver->max_var);
  lit *= sign;
  return ch;
}

void Parser::parse_dimacs () {
  int ch;
  START (parse);
  for (;;) {
    ch = parse_char ();
    if (ch != 'c') break;
    while ((ch = parse_char ()) != '\n')
      if (ch == EOF)
        PER ("unexpected end-of-file in header comment");
  }
  if (ch != 'p') PER ("expected 'c' or 'p'");
  parse_string (" cnf ", 'p');
  if (!isdigit (ch = parse_char ())) PER ("expected digit after 'p cnf '");
  ch = parse_positive_int (ch, solver->max_var, "<max-var>");
  if (ch != ' ') PER ("expected ' ' after 'p cnf %d'", solver->max_var);
  if (!isdigit (ch = parse_char ()))
    PER ("expected digit after 'p cnf %d '", solver->max_var);
  ch = parse_positive_int (ch, solver->num_original_clauses, "<num-clauses>");
  while (ch == ' ' || ch == '\r') ch = parse_char ();
  if (ch != '\n')
    PER ("expected new-line after 'p cnf %d %d'",
      solver->max_var, solver->num_original_clauses);
  MSG ("found 'p cnf %d %d' header", solver->max_var, solver->num_original_clauses);
  solver->init_variables ();
  int lit = 0, parsed_clauses = 0;
  while ((ch = parse_char ()) != EOF) {
    if (ch == ' ' || ch == '\n' || ch == '\t' || ch == '\r') continue;
    if (ch == 'c') {
COMMENT:
      while ((ch = parse_char ()) != '\n')
        if (ch == EOF) PER ("unexpected end-of-file in body comment");
      continue;
    }
    if (parse_lit (ch, lit) == 'c') goto COMMENT;
#ifndef NDEBUG
    solver->original_literals.push_back (lit);
#endif
    if (lit) {
      if (solver->clause.size () == INT_MAX) PER ("clause too large");
      solver->clause.push_back (lit);
    } else {
      if (!solver->tautological_clause ())
        solver->add_new_original_clause ();
      else LOG ("tautological original clause");
      solver->clause.clear ();
      if (parsed_clauses++ >= solver->num_original_clauses)
        PER ("too many clauses");
    }
  }
  if (lit) PER ("last clause without '0'");
  if (parsed_clauses < solver->num_original_clauses) PER ("clause missing");
  MSG ("parsed %d clauses in %.2f seconds", parsed_clauses, solver->seconds ());
  STOP (parse);
}

};
