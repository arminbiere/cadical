#ifndef _logging_hpp_INCLUDED
#define _logging_hpp_INCLUDED

#ifdef LOGGING

#include <vector>

namespace CaDiCaL {

// You might want to turn on logging with './configure -l'.

using namespace std;

struct Clause;
class Solver;

struct Logger {
static void log (Solver *, const char * fmt, ...);
static void log (Solver *, const Clause *, const char *fmt, ...);
static void log (Solver *, const vector<int> &, const char *fmt, ...);
};

};

#define LOG(ARGS...) do { Logger::log (solver, ##ARGS); } while (0)

#else
#define LOG(ARGS...) do { } while (0)
#endif

#endif
