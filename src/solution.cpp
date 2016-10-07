#include "solver.hpp"

namespace CaDiCaL {

// Sam Buss suggested to debug the case where a solver incorrectly claims the
// formula to be unsatisfiable by checking every learned clause to be satisfied by
// a satisfying assignment.  Thus the first inconsistent learned clause will be
// immediately flagged without the need to generate proof traces and perform
// forward proof checking.  The incorrectly derived clause will raise an abort
// signal and thus allows to debug the issue with a symbolic debugger immediately.

void Parser::parse_solution () {
  START (parse);
  NEW (solver->solution, signed char, solver->max_var + 1);
  for (int i = 1; i <= solver->max_var; i++) solver->solution[i] = 0;
  int ch;
  for (;;) {
    ch = parse_char ();
    if (ch == EOF) PER ("missing 's' line");
    if (ch == 'c') {
      while ((ch = parse_char ()) != '\n')
        if (ch == EOF) PER ("unexpected end-of-file in comment");
    }
    if (ch == 's') break;
    PER ("expected 'c' or 's'");
  }
  parse_string (" SATISFIABLE", 's');
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
      if ((ch = parse_lit (ch, lit)) == 'c') PER ("unexpected comment");
      if (!lit) break;
      if (solver->solution[abs (lit)])
        PER ("variable %d occurs twice", abs (lit));
      LOG ("solution %d", lit);
      solver->solution [abs (lit)] = sign (lit);
      count++;
      if (ch == '\r') ch = parse_char ();
    } while (ch != '\n');
    if (!lit) break;
  }
  MSG ("parsed %d solutions %.2f%%",
    count, percent (count, solver->max_var));
  STOP (parse);
}

int Solver::sol (int lit) {
  assert (solution);
  int res = solution[vidx (lit)];
  if (lit < 0) res = -res;
  return res;
}

void Solver::check_clause () {
  if (!solution) return;
  bool satisfied = false;
  for (size_t i = 0; !satisfied && i < clause.size (); i++)
    satisfied = (sol (clause[i]) > 0);
  if (satisfied) return;
  fflush (stdout);
  fputs (
    "*** cadical error: learned clause unsatisfied by solution:\n",
    stderr);
  for (size_t i = 0; i < clause.size (); i++)
    fprintf (stderr, "%d ", clause[i]);
  fputs ("0\n", stderr);
  fflush (stderr);
  abort ();
}

};
