#ifndef _logging_hpp_INCLUDED
#define _logging_hpp_INCLUDED

namespace CaDiCaL {

// You might want to turn on logging with './configure -l'.

#ifdef LOGGING

#include <vector>

struct Clause;

void LOG (const char * fmt, ...);
void LOG (Clause * c, const char *fmt, ...);
void LOG (const vector<int> & clause, const char *fmt, ...);

#else
#define LOG(ARGS...) do { } while (0)
#endif

};

#endif
