#ifndef _util_hpp_INCLUDED
#define _util_hpp_INCLUDED

namespace CaDiCaL {

inline double relative (double a, double b) { return b ? a / b : 0; }
inline double percent (double a, double b) { return relative (100 * a, b); }
inline int sign (int lit) { return (lit > 0) - (lit < 0); }

bool is_int_str (const char * str);
bool is_double_str (const char * str);

bool has_suffix (const char * str, const char * suffix);

};

#endif
