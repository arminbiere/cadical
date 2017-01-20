#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Initialize all the options to their default value 'V'.

Options::Options (Internal * s) : internal (s) {
#define OPTION(N,T,V,L,H,D) \
  N = (T) (V);
  OPTIONS
#undef OPTION
}

/*------------------------------------------------------------------------*/

// Functions to work with command line option style format.

bool Options::set (bool & opt, const char * name,
                   const char * valstr, const bool l, const bool h) {
  assert (!l), assert (h);
       if (!strcmp (valstr, "true")  || !strcmp (valstr, "1")) opt = true;
  else if (!strcmp (valstr, "false") || !strcmp (valstr, "0")) opt = false;
  else return false;
  LOG ("set option --%s=%d from (const char*) \"%s\"", name, opt, valstr);
  return true;
}

bool Options::set (int & opt, const char * name,
                   const char * valstr, const int l, const int h) {
  assert (l < h);
  if (!is_int_str (valstr)) return false;
  int val = atoi (valstr);
  if (val < l) val = l;
  if (val > h) val = h;
  opt = val;
  LOG ("set option --%s=%d from (const char*) \"%s\"", name, opt, valstr);
  return true;
}

bool Options::set (double & opt, const char * name,
                   const char * valstr,
                   const double l, const double h) {
  assert (l < h);
  if (!is_double_str (valstr)) return false;
  double val = atof (valstr);
  if (val < l) val = l;
  if (val > h) val = h;
  opt = val;
  LOG ("set option --%s=%g from (const char*) \"%s\"", name, opt, valstr);
  return true;
}

const char * Options::match (const char * arg, const char * name) {
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
  if ((valstr = match (arg, # N))) \
    return set (N, # N, valstr, L, H); \
  else
  OPTIONS
#undef OPTION
  return false;
}

/*------------------------------------------------------------------------*/

#define OPTION_FORMAT_bool   "%s"
#define OPTION_FORMAT_int    "%d"
#define OPTION_FORMAT_double "%g"

#define OPTION_CONVERT_bool(V)    ((V) ? "true" : "false")
#define OPTION_CONVERT_int(V)     ((int)(V))
#define OPTION_CONVERT_double(V)  ((double)(V))

/*------------------------------------------------------------------------*/

// More generic interface with 'double' values.

bool Options::has (const char * name) {
#define OPTION(N,T,V,L,H,D) \
  if (!strcmp (name, #N)) return true; else
  OPTIONS
#undef OPTION
  return false;
}

bool Options::set (const char * name, double val) {
#define OPTION(N,T,V,L,H,D) \
  if (!strcmp (name, #N)) { \
    if (val < L) val = L; \
    if (val > H) val = H; \
    N = val; \
    LOG ("set option --%s=" OPTION_FORMAT_ ## T " from (double) %g", \
      OPTION_CONVERT_ ## T (N), val); \
  }
  OPTIONS
#undef OPTION
  return false;
}

double Options::get (const char * name) {
#define OPTION(N,T,V,L,H,D) \
  if (!strcmp (name, #N)) return N; else
  OPTIONS
#undef OPTION
  return 0;
}

/*------------------------------------------------------------------------*/

void Options::print () {
  unsigned different = 0;
#ifdef QUIET
  const bool verbose = false;
#endif
#define OPTION(N,T,V,L,H,D) \
  if (N != (V)) different++; \
  if (verbose || N != (V)) { \
    MSG ("--" #N "=" OPTION_FORMAT_ ## T \
         "  (%s default " OPTION_FORMAT_ ## T ")", \
	 OPTION_CONVERT_ ## T (N), \
	 (N == (V)) ? "same as" : "different from", \
	 OPTION_CONVERT_ ## T (V)); \
  }
  OPTIONS
#undef OPTION
  if (!different) MSG ("all options are set to their default value");
}

void Options::usage () {
#define OPTION(N,T,V,L,H,D) \
  printf ( \
    "  %-26s " D " [" OPTION_FORMAT_ ## T "]\n", \
    "--" #N "=<" #T ">", OPTION_CONVERT_ ## T ((T)(V)));
  OPTIONS
#undef OPTION
}

/*------------------------------------------------------------------------*/

};
