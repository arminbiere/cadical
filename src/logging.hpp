#ifndef _logging_hpp_INCLUDED
#define _logging_hpp_INCLUDED

#ifdef LOGGING

#include <vector>

namespace CaDiCaL {

// For debugging purposes and to help understanding what the solver is doing
// there is a logging facility which is compiled in by './configure -l'.  It
// still has to be enabled at run-time though (again using the '-l' option
// in the stand-alone solver).  It produces quite a bit of information.

using namespace std;

struct Clause;
class Internal;

struct Logger {

// Simple logging of a C-style format string.
//
static void log (Internal *, const char * fmt, ...);

// Prints the format string (with its argument) and then the clause.  The
// clause can also be a zero pointer and then is interpreted as a decision
// (current decision level > 0) or unit clause (zero decision level) and
// printed accordingly.
//
static void log (Internal *, const Clause *, const char *fmt, ...);

// Same as before, except that this is meant for the global 'clause' stack
// used for new clauses (and not for reasons).
//
static void log (Internal *, const vector<int> &, const char *fmt, ...);

};

};

/*------------------------------------------------------------------------*/

// Make sure that 'logging' code is really not included (second case of the
// '#ifdef') if logging code is not included.

#define LOG(ARGS...) \
do {  \
  if (!internal->opts.log) break; \
  Logger::log (internal, ##ARGS); \
} while (0)

#else
#define LOG(ARGS...) do { } while (0)
#endif

/*------------------------------------------------------------------------*/

#endif
