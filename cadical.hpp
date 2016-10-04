#ifndef _cadical_hpp_INCLUDED
#define _cadical_hpp_INCLUDED

#include <vector>

using namespace std;

#include <climits>
#include <cassert>

#include "options.hpp"
#include "clause.hpp"
#include "var.hpp"
#include "watch.hpp"
#include "ema.hpp"
#include "avg.hpp"
#include "level.hpp"
#include "timer.hpp"
#include "parse.hpp"
#include "proof.hpp"

namespace CaDiCaL {

class Solver {

  Options opts;
  int max_var;
  int num_original_clauses;
  vector<int> original_literals;
  Var * vars;
  signed char * vals;
  signed char * phases;

  // VMTF decision queue

  struct {
    int first, last;    // anchors (head/tail) for doubly linked list
    int assigned;       // all variables after this one are assigned
  } queue;

  bool unsat;           // empty clause found or learned
  int level;            // decision level (levels.size () - 1)
  vector<Level> levels; // 'level + 1 == levels.size ()'
  vector<int> trail;    // assigned literals

  struct {
    size_t binaries;    // next literal position on trail for binaries
    size_t watches;     // next literal position on trail for watches
  } next;

  vector<int> clause;      // temporary clause in parsing & learning
  vector<Clause*> clauses; // ordered collection of all clauses
  bool iterating;          // report top-level assigned variables

  struct {
    vector<int> literals;  // seen & bumped literals in 'analyze'
    vector<int> levels;    // decision levels of 1st UIP clause
    vector<int> minimized; // marked removable or poison in 'minmize'
  } seen;

  vector<Clause*> resolved; // large clauses in 'analyze'
  Clause * conflict;        // set in 'propagation', reset in 'analyze'
  bool clashing_unit;       // set in 'parse_dimacs'

  struct {
    long conflicts;
    long decisions;
    long propagations;    // propagated literals in 'propagate'

    struct {
      long count;         // actual number of happened restarts 
      long tried;         // number of tried restarts
      long unit;          // from those the number forced by low unit frequency
      long blocked;       // blocked restart intervals in 'analyze'
      long unforced;      // not forced (slow glue > fast glue)
      long forced;        // forced (slow glue < fast glue)
      long reused;        // number of time trail was (partially) reused
    } restart;

    long reports, sections;

    long bumped;                  // seen and bumped variables in 'analyze'
    long resolved;                // resolved redundant clauses in 'analyze'
    long searched;                // searched decisions in 'decide'

    struct { long count, clauses, bytes; } reduce; // in 'reduce'
    struct { long learned, minimized; } literals;  // in 'minimize_clause'

    struct { long redundant, irredundant, current, max; } clauses;
    struct { struct { size_t current, max; } total, watcher; } bytes;

    struct { long unit, binary; } learned;

    int fixed;                    // top level assigned variables
  } stats;

#ifdef PROFILING
  vector<Timer> timers;
#endif

  // Averages to control which clauses are collected in 'reduce' and when to
  // force and delay 'restart' respectively.  Most of them are exponential
  // moving average, but for the slow glue we use an actual average.

  struct {
    struct { EMA unit; } frequency;
    struct { EMA fast; AVG slow, blocking, nonblocking; } glue;
    EMA trail;
    AVG jump;
  } avg;

  struct { bool enabled, exploring; } blocking;

  // Limits for next restart, reduce.

  struct {
    struct { long conflicts, resolved; int fixed; } reduce;
    struct { long conflicts; } restart;
    long blocking;
  } limits;

  // Increments for next restart, reduce interval.

  struct {
    long reduce, blocking;
    double unit;
  } inc;

#ifndef NDEBUG

  // Sam Buss suggested to debug the case where a solver incorrectly claims
  // the formula to be unsatisfiable by checking every learned clause to be
  // satisfied by a satisfying assignment.  Thus the first inconsistent
  // learned clause will be immediately flagged without the need to generate
  // proof traces and perform forward proof checking.  The incorrectly derived
  // clause will raise an abort signal and thus allows to debug the issue with
  // a symbolic debugger immediately.

  signed char * solution;          // like 'vals' (and 'phases')

#endif

  Proof * proof;
};

};

#endif
