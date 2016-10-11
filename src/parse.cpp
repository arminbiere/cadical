#include "parse.hpp"
#include "internal.hpp"
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

const char * Parser::parse_string (const char * str, char prev) {
  for (const char * p = str; *p; p++)
    if (parse_char () == *p) prev = *p;
    else PER ("expected '%c' after '%c'", *p, prev);
  return 0;
}

const char *
Parser::parse_positive_int (int & ch, int & res, const char * name) {
  assert (isdigit (ch));
  res = ch - '0';
  while (isdigit (ch = parse_char ())) {
    int digit = ch - '0';
    if (INT_MAX/10 < res || INT_MAX - digit < 10*res)
      PER ("too large '%s' in header", name);
    res = 10*res + digit;
  }
  return 0;
}

const char * Parser::parse_lit (int & ch, int & lit) {
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
  if (lit > internal->max_var)
    PER ("literal %d exceeds maximum variable %d",
      sign*lit, internal->max_var);
  lit *= sign;
  return 0;
}

const char * Parser::parse_dimacs_non_profiled () {
  int ch, num_original_clauses = 0;
  for (;;) {
    ch = parse_char ();
    if (ch != 'c') break;
    while ((ch = parse_char ()) != '\n')
      if (ch == EOF)
        PER ("unexpected end-of-file in header comment");
  }
  if (ch != 'p') PER ("expected 'c' or 'p'");
  const char * err = parse_string (" cnf ", 'p');
  if (err) return err;
  if (!isdigit (ch = parse_char ())) PER ("expected digit after 'p cnf '");
  err = parse_positive_int (ch, internal->max_var, "<max-var>");
  if (err) return err;
  if (ch != ' ') PER ("expected ' ' after 'p cnf %d'", internal->max_var);
  if (!isdigit (ch = parse_char ()))
    PER ("expected digit after 'p cnf %d '", internal->max_var);
  err = parse_positive_int (ch, num_original_clauses, "<num-clauses>");
  if (err) return err;
  while (ch == ' ' || ch == '\r') ch = parse_char ();
  if (ch != '\n')
    PER ("expected new-line after 'p cnf %d %d'",
      internal->max_var, num_original_clauses);
  MSG ("found 'p cnf %d %d' header",
    internal->max_var, num_original_clauses);
  internal->init_variables ();
  int lit = 0, parsed_clauses = 0;
  while ((ch = parse_char ()) != EOF) {
    if (ch == ' ' || ch == '\n' || ch == '\t' || ch == '\r') continue;
    if (ch == 'c') {
COMMENT:
      while ((ch = parse_char ()) != '\n')
        if (ch == EOF) PER ("unexpected end-of-file in body comment");
      continue;
    }
    err = parse_lit (ch, lit);
    if (err) return err;
    if (ch == 'c') goto COMMENT;
    internal->original.push_back (lit);
    if (lit) {
      if (internal->clause.size () == INT_MAX) PER ("clause too large");
      internal->clause.push_back (lit);
    } else {
      if (!internal->tautological_clause ())
        internal->add_new_original_clause ();
      else LOG ("tautological original clause");
      internal->clause.clear ();
      if (parsed_clauses++ >= num_original_clauses)
        PER ("too many clauses");
    }
  }
  if (lit) PER ("last clause without '0'");
  if (parsed_clauses < num_original_clauses) PER ("clause missing");
  MSG ("parsed %d clauses in %.2f seconds",
    parsed_clauses, internal->seconds ());
  return 0;
}

const char * Parser::parse_dimacs () {
  START (parse);
  const char * err = parse_dimacs_non_profiled ();
  STOP (parse);
  return err;
}

};
