#ifndef _logging_hpp_INCLUDED
#define _logging_hpp_INCLUDED

#ifdef LOGGING

#include <vector>

namespace CaDiCaL {

// You might want to turn on logging with './configure -l'.

using namespace std;

struct Clause;
class Internal;

struct Logger {
static void log (Internal *, const char * fmt, ...);
static void log (Internal *, const Clause *, const char *fmt, ...);
static void log (Internal *, const vector<int> &, const char *fmt, ...);
};

};

#define LOG(ARGS...) do { Logger::log (internal, ##ARGS); } while (0)

#else
#define LOG(ARGS...) do { } while (0)
#endif

#endif
