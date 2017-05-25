#include "internal.hpp"

/*------------------------------------------------------------------------*/

// Only used here for error reporting, so also only included here.

#include <string>

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Parsing utilities.

int Parser::parse_char () { return file->get (); }

// Return an non zero error string if a parse error occurred.

inline const char *
Parser::parse_string (const char * str, char prev) {
  for (const char * p = str; *p; p++)
    if (parse_char () == *p) prev = *p;
    else PER ("expected '%c' after '%c'", *p, prev);
  return 0;
}

inline const char *
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

inline const char *
Parser::parse_lit (int & ch, int & lit, const int vars) {
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
  if (ch != 'c' && ch != ' ' && ch != '\t' && ch != '\n' && ch != EOF)
    PER ("expected white space after '%d'", sign*lit);
  if (lit > vars)
    PER ("literal %d exceeds maximum variable %d", sign*lit, vars);
  lit *= sign;
  return 0;
}

/*------------------------------------------------------------------------*/

// Parsing function for CNF in DIMACS format.

const char * Parser::parse_dimacs_non_profiled () {
  int ch, vars = 0, clauses = 0;
  for (;;) {
    ch = parse_char ();
    if (ch != 'c') break;
    string buf;
    while ((ch = parse_char ()) != '\n')
      if (ch == EOF) PER ("unexpected end-of-file in header comment");
      else if (ch != '\r') buf.push_back (ch);
    const char * o;
    for (o = buf.c_str (); *o && *o != '-'; o++)
      ;
    if (!*o) continue;
    VRB ("parse-dimacs", "found option '%s'", o);
    if (*o) internal->opts.set (o);
  }
  if (ch != 'p') PER ("expected 'c' or 'p'");
  const char * err = parse_string (" cnf ", 'p');
  if (err) return err;
  if (!isdigit (ch = parse_char ())) PER ("expected digit after 'p cnf '");
  err = parse_positive_int (ch, vars, "<max-var>");
  if (err) return err;
  if (ch != ' ') PER ("expected ' ' after 'p cnf %d'", vars);
  if (!isdigit (ch = parse_char ()))
    PER ("expected digit after 'p cnf %d '", vars);
  err = parse_positive_int (ch, clauses, "<num-clauses>");
  if (err) return err;
  while (ch == ' ' || ch == '\r') ch = parse_char ();
  if (ch != '\n')
    PER ("expected new-line after 'p cnf %d %d'", vars, clauses);
  MSG ("found 'p cnf %d %d' header", vars, clauses);
  external->init (vars);
  int lit = 0, parsed = 0;
  while ((ch = parse_char ()) != EOF) {
    if (ch == ' ' || ch == '\n' || ch == '\t' || ch == '\r') continue;
    if (ch == 'c') {
COMMENT:
      while ((ch = parse_char ()) != '\n')
        if (ch == EOF) PER ("unexpected end-of-file in body comment");
      continue;
    }
    err = parse_lit (ch, lit, vars);
    if (err) return err;
    if (ch == 'c') goto COMMENT;
    external->add (lit);
    if (!lit && parsed++ >= clauses && !internal->opts.force)
      PER ("too many clauses");
  }
  if (lit) PER ("last clause without '0'");
  if (parsed < clauses && !internal->opts.force) PER ("clause missing");
  MSG ("parsed %d clauses in %.2f seconds", parsed, process_time ());
  return 0;
}

/*------------------------------------------------------------------------*/

// Parsing function for a solution in competition output format.

const char * Parser::parse_solution_non_profiled () {
  NEW_ZERO (external->solution, signed_char, external->max_var + 1);
  int ch;
  for (;;) {
    ch = parse_char ();
    if (ch == EOF) PER ("missing 's' line");
    else if (ch == 'c') {
      while ((ch = parse_char ()) != '\n')
        if (ch == EOF) PER ("unexpected end-of-file in comment");
    } else if (ch == 's') break;
    else PER ("expected 'c' or 's'");
  }
  const char * err = parse_string (" SATISFIABLE", 's');
  if (err) return err;
  if ((ch = parse_char ()) == '\r') ch = parse_char ();
  if (ch != '\n') PER ("expected new-line after 's SATISFIABLE'");
  int count = 0;
  for (;;) {
    ch = parse_char ();
    if (ch != 'v') PER ("expected 'v' at start-of-line");
    if ((ch = parse_char ()) != ' ') PER ("expected ' ' after 'v'");
    int lit = 0; ch = parse_char ();
    do {
      if (ch == ' ' || ch == '\t') { ch = parse_char (); continue; }
      err = parse_lit (ch, lit, external->max_var);
      if (err) return err;
      if (ch == 'c') PER ("unexpected comment");
      if (!lit) break;
      if (external->solution[abs (lit)])
        PER ("variable %d occurs twice", abs (lit));
      LOG ("solution %d", lit);
      external->solution [abs (lit)] = sign (lit);
      count++;
      if (ch == '\r') ch = parse_char ();
    } while (ch != '\n');
    if (!lit) break;
  }
  MSG ("parsed %d solutions %.2f%%",
    count, percent (count, external->max_var));
  return 0;
}

/*------------------------------------------------------------------------*/

// Wrappers to profile parsing and at the same time use the convenient
// implicit 'return' in PER in the non-profiled versions.

const char * Parser::parse_dimacs () {
  START (parse);
  const char * err = parse_dimacs_non_profiled ();
  STOP (parse);
  return err;
}

const char * Parser::parse_solution () {
  START (parse);
  const char * err = parse_solution_non_profiled ();
  STOP (parse);
  return err;
}

};
