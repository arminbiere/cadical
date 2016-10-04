#include "options.hpp"

#include <cassert>
#include <cstring>
#include <cstdlib>

namespace CaDiCaL {

Options::Options () {
#define OPTION(N,T,V,L,H,D) \
  N = (T) (V);
  OPTIONS
#undef OPTION
}

#define LOG(...) do { } while(0)

static bool set_option (bool & opt, const char * name,
                        const char * valstr, const bool l, const bool h) {
  assert (!l), assert (h);
       if (!strcmp (valstr, "true")  || !strcmp (valstr, "1")) opt = true;
  else if (!strcmp (valstr, "false") || !strcmp (valstr, "0")) opt = false;
  else return false;
  LOG ("set option --%s=%d", name, opt);
  return true;
}

static bool set_option (int & opt, const char * name,
                        const char * valstr, const int l, const int h) {
  assert (l < h);
  int val = atoi (valstr);              // TODO check valstr to be valid
  if (val < l) val = l;
  if (val > h) val = h;
  opt = val;
  LOG ("set option --%s=%d", name, opt);
  return true;
}

static bool set_option (double & opt, const char * name,
                        const char * valstr,
                        const double l, const double h) {
  assert (l < h);
  double val = atof (valstr);           // TODO check valstr to be valid
  if (val < l) val = l;
  if (val > h) val = h;
  opt = val;
  LOG ("set option --%s=%g", name, opt);
  return true;
}

static const char *
match_option (const char * arg, const char * name) {
  if (arg[0] != '-' || arg[1] != '-') return 0;
  const bool no = (arg[2] == 'n' && arg[3] == 'o' && arg[4] == '-');
  const char * p = arg + (no ? 5 : 2), * q = name;
  while (*q) if (*q++ != *p++) return 0;
  if (!*p) return no ? "0" : "1";
  if (*p++ != '=') return 0;
  return p;
}

bool Options::set (const char * arg) {
  const char * valstr;
#define OPTION(N,T,V,L,H,D) \
  if ((valstr = match_option (arg, # N))) \
    return set_option (N, # N, valstr, L, H); \
  else
  OPTIONS
#undef OPTION
  return false;
}

};


