#include "internal.hpp"

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Parse error.

#define PER(...) \
do { \
  internal->error_message.init (\
    "%s:%d: parse error: ", \
    file->name (), (int) file->lineno ()); \
  return internal->error_message.append (__VA_ARGS__); \
} while (0)

/*------------------------------------------------------------------------*/

// Parsing utilities.

inline int Parser::parse_char () { return file->get (); }

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
Parser::parse_lit (int & ch, int & lit, const int vars, int strict) {
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
  if (lit > vars && strict > 0)
    PER ("literal %d exceeds maximum variable %d", sign*lit, vars);
  lit *= sign;
  return 0;
}

/*------------------------------------------------------------------------*/

// Parsing CNF in DIMACS format.

const char * Parser::parse_dimacs_non_profiled (int & vars, int strict) {

#ifndef QUIET
  const double start = internal->time ();
#endif

  int ch, clauses = 0;
  vars = 0;

  // First read comments before header with possibly embedded options.
  //
  for (;;) {
    ch = parse_char ();
    if (ch == ' ' || ch == '\n' || ch == '\t' || ch == '\r') continue;
    if (ch != 'c') break;
    string buf;
    while ((ch = parse_char ()) != '\n')
      if (ch == EOF) PER ("unexpected end-of-file in header comment");
      else if (ch != '\r') buf.push_back (ch);
    const char * o;
    for (o = buf.c_str (); *o && *o != '-'; o++)
      ;
    if (!*o) continue;
    PHASE ("parse-dimacs", "found option '%s'", o);
    if (*o) solver->set_long_option (o);
  }

  // Now read 'p cnf <var> <clauses>' header of DIMACS file.
  //
  if (ch != 'p') PER ("expected 'c' or 'p'");

  if (strict > 1) {
    const char * err = parse_string (" cnf ", 'p');
    if (err) return err;
    ch = parse_char ();
    if (!isdigit (ch)) PER ("expected digit after 'p cnf '");
    err = parse_positive_int (ch, vars, "<max-var>");
    if (err) return err;
    if (ch != ' ') PER ("expected ' ' after 'p cnf %d'", vars);
    if (!isdigit (ch = parse_char ()))
      PER ("expected digit after 'p cnf %d '", vars);
    err = parse_positive_int (ch, clauses, "<num-clauses>");
    if (err) return err;
    if (ch != '\n')
      PER ("expected new-line after 'p cnf %d %d'", vars, clauses);
  } else {
    ch = parse_char ();
    if (!isspace (ch)) PER ("expected space after 'p'");
    do ch = parse_char (); while (isspace (ch));
    if (ch != 'c') PER ("expected 'c' after 'p '");
    if (parse_char () != 'n') PER ("expected 'n' after 'p c'");
    if (parse_char () != 'f') PER ("expected 'f' after 'p cn'");
    ch = parse_char ();
    if (!isspace (ch)) PER ("expected space after 'p cnf'");
    do ch = parse_char (); while (isspace (ch));
    if (!isdigit (ch)) PER ("expected digit after 'p cnf '");
    const char * err = parse_positive_int (ch, vars, "<max-var>");
    if (err) return err;
    if (!isspace (ch)) PER ("expected space after 'p cnf %d'", vars);
    do ch = parse_char (); while (isspace (ch));
    if (!isdigit (ch)) PER ("expected digit after 'p cnf %d '", vars);
    err = parse_positive_int (ch, clauses, "<num-clauses>");
    if (err) return err;
    while (ch != '\n') {
      if (ch != '\r' && !isspace (ch))
        PER ("expected new-line after 'p cnf %d %d'", vars, clauses);
      ch = parse_char ();
    }
  }

  MSG ("found %s'p cnf %d %d'%s header",
    tout.green_code (), vars, clauses, tout.normal_code ());

  solver->reserve (vars);

  // Now read body of DIMACS file.
  //
  // external->init (vars);
  int lit = 0, parsed = 0;
  while ((ch = parse_char ()) != EOF) {
    if (ch == ' ' || ch == '\n' || ch == '\t' || ch == '\r') continue;
    if (ch == 'c') {
      while ((ch = parse_char ()) != '\n' && ch != EOF)
        ;
      if (ch == EOF) break;
      continue;
    }
    const char * err = parse_lit (ch, lit, vars, strict);
    if (err) return err;
    if (ch == 'c') {
      while ((ch = parse_char ()) != '\n')
        if (ch == EOF)
          PER ("unexpected end-of-file in comment");
    }
    solver->add (lit);
    if (!lit && parsed++ >= clauses && strict > 0)
      PER ("too many clauses");
  }
  if (lit) PER ("last clause without terminating '0'");
  if (parsed < clauses && strict > 0) PER ("clause missing");

#ifndef QUIET
  const double end = internal->time ();
  MSG ("parsed %d clauses in %.2f seconds %s time",
    parsed, end - start, internal->opts.realtime ? "real" : "process");
#endif

  return 0;
}

/*------------------------------------------------------------------------*/

// Parsing solution in competition output format.

const char * Parser::parse_solution_non_profiled () {
  external->solution = new signed char [ external->max_var + 1 ];
  clear_n (external->solution, external->max_var + 1);
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
      err = parse_lit (ch, lit, external->max_var, false);
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
  MSG ("parsed %d values %.2f%%",
    count, percent (count, external->max_var));
  return 0;
}

/*------------------------------------------------------------------------*/

// Wrappers to profile parsing and at the same time use the convenient
// implicit 'return' in PER in the non-profiled versions.

const char * Parser::parse_dimacs (int & vars, int strict) {
  START (parse);
  const char * err = parse_dimacs_non_profiled (vars, strict);
  STOP (parse);
  return err;
}

const char * Parser::parse_solution () {
  START (parse);
  const char * err = parse_solution_non_profiled ();
  STOP (parse);
  return err;
}

}
