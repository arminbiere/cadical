#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// By default, e.g., for library usage, the 'opts.report' value is zero
// ('false') but can be set to '1' by the stand alone solver.  Using here
// a static default value avoids that the stand alone solver reports that
// '--report=1' is different from the default in 'print ()' below.
//
int Options::report_default_value;

/*------------------------------------------------------------------------*/

// The order of initializations of static objects is undefined and thus we
// can not assume that this table is already initialized if a solver and
// thus the constructor of 'Options' is called.  Therefore we just have to
// reinitialize this table in every call to 'Options::Options'.  This does
// not produce a data race even for parallel initialization since the
// same values are written by all threads under the assumption that the
// 'report_default_value' is set before any solver is initialized.  We do
// have to perform this static initialization though, since 'has' is
// static and does not require that the 'Options' constructor was called.

Option Options::table [] = {
#define OPTION(N,V,L,H,O,D) \
  { #N, (int) V, (int) L, (int) H, (int) O, D },
  OPTIONS
#undef OPTION
};

/*------------------------------------------------------------------------*/

// Binary search in 'table', which requires option names to be sorted, which
// in turned is checked at start-up in 'Options::Options'.

Option * Options::has (const char * name) {
  size_t l = 0, r = number_of_options;
  while (l < r) {
    size_t m = l + (r - l)/2;
    Option * res = &table[m];
    int tmp = strcmp (name, res->name);
    if (!tmp) return res;
    if (tmp < 0) r = m;
    if (tmp > 0) l = m + 1;
  }
  return 0;
}

/*------------------------------------------------------------------------*/

bool Options::parse_option_value (const char * val_str, int & val) {
  if (!strcmp (val_str, "true")) val = 1;
  else if (!strcmp (val_str, "false")) val = 0;
  else {
    const char * p = val_str;
    int sign;

    if (*p == '-') sign = -1, p++;
    else sign = 1;

    int ch;
    if (!isdigit ((ch = *p++))) return false;

    const int64_t bound = - (int64_t) INT_MIN;
    int64_t mantissa = ch - '0';

    while (isdigit (ch = *p++)) {
      if (bound / 10 < mantissa) mantissa = bound;
      else mantissa *= 10;
      const int digit = ch - '0';
      if (bound - digit < mantissa) mantissa = bound;
      else mantissa += digit;
    }

    int exponent = 0;
    if (ch  == 'e') {
      while (isdigit ((ch = *p++)))
        exponent = exponent ? 10 : ch - '0';
      if (ch) return false;
    } else if (ch) return false;

    assert (exponent <= 10);
    int64_t val64 = mantissa;
    for (int i = 0; i < exponent; i++) val64 *= 10;

    if (sign < 0) {
      val64 = -val64;
      if (val64 < INT_MIN) val64 = INT_MIN;
    } else {
      if (val64 > INT_MAX) val64 = INT_MAX;
    }

    assert (INT_MIN <= val64);
    assert (val64 <= INT_MAX);

    val = val64;
  }
  return true;
}

bool Options::parse_long_option (const char * arg,
                                 string & name, int & val) {
  if (arg[0] != '-' || arg[1] != '-') return false;
  const bool has_no_prefix =
    (arg[2] == 'n' && arg[3] == 'o' && arg[4] == '-');
  const size_t offset = has_no_prefix ? 5 : 2;
  name = arg + offset;
  const size_t pos = name.find_first_of ('=');
  if (pos != string::npos) name[pos] = 0;
  if (!Options::has (name.c_str ())) return false;
  if (pos == string::npos) val = !has_no_prefix;
  else {
    const char * val_str = name.c_str () + pos + 1;
    if (!parse_option_value (val_str, val)) return false;
  }
  return true;
}

/*------------------------------------------------------------------------*/

void Options::initialize_from_environment (
  int & val, const char * name, const int L, const int H)
{
  char key[80], * q;
  const char * p;
  assert (strlen (name) + strlen ("CADICAL_") + 1 < sizeof (key));
  for (p = "CADICAL_", q = key; *p; p++)
    *q++ = *p;
  for (p = name; *p; p++)
    *q++ = toupper (*p);
  assert (q < key + sizeof (key));
  *q = 0;
  const char * val_str = getenv (key);
  if (!val_str) return;
  if (!parse_option_value (val_str, val)) return;
  if (val < L) val = L;
  if (val > H) val = H;
}

// Initialize all the options to their default value 'V'.

Options::Options (Internal * s) : internal (s)
{
  assert (number_of_options == sizeof Options::table / sizeof (Option));

  // First initialize them according to defaults in 'options.hpp'.
  //
  const char * prev = "";
  size_t i = 0;
# define OPTION(N,V,L,H,O,D) \
  do { \
    if ((L) > (V)) \
      FATAL ("'" #N "' default '" #V "' " \
        "lower minimum '" #L "' in 'options.hpp'"); \
    if ((H) < (V)) \
      FATAL ("'" #N "' default '" #V "' " \
        "larger maximum '" #H "' in 'options.hpp'"); \
    if (strcmp (prev, #N) > 0)  \
      FATAL ("'%s' ordered before '" #N "' in 'options.hpp'", prev); \
    N = (int)(V); \
    assert (&val (i) == &N); \
    /* The order of initializing static data is undefined and thus */ \
    /* it might be the case that the 'table' is not initialized yet. */ \
    /* Thus this construction just reinitializes the table too even */ \
    /* though it might not be necessary. */ \
    assert (!table[i].name || !strcmp (table[i].name, #N)); \
    table[i] = { #N, (int)(V), (int)(L), (int)(H), (int)(O), D }; \
    prev = #N; \
    i++; \
  } while (0);
  OPTIONS
# undef OPTION

  // Check consistency in debugging mode.
  //
#ifndef NDEBUG
  assert (i == number_of_options);
  assert (!has ("aaaaa"));
  assert (!has ("non-existing-option"));
  assert (!has ("zzzzz"));
#endif

  // Now overwrite default options with environment values.
  //
# define OPTION(N,V,L,H,O,D) \
  initialize_from_environment (N, #N, L, H);
  OPTIONS
# undef OPTION
}

/*------------------------------------------------------------------------*/

void Options::set (Option * o, int new_val) {
  assert (o);
  int & val = o->val (this), old_val = val;
  if (old_val == new_val) {
    LOG ("keeping value '%d' of option '%s'", old_val, o->name);
    return;
  }
  if (new_val < o->lo) {
    LOG ("bounding '%d' to lower limit '%d' for option '%s'",
      new_val, o->lo, o->name);
    new_val = o->lo;
  }
  if (new_val > o->hi) {
    LOG ("bounding '%d' to upper limit '%d' for option '%s'",
      new_val, o->hi, o->name);
    new_val = o->hi;
  }
  val = new_val;
  LOG ("set option 'set (\"%s\", %d)' from '%d'",
    o->name, new_val, old_val);
}

// Explicit option value setting.

bool Options::set (const char * name, int val) {
  Option * o = has (name);
  if (!o) return false;
  set (o, val);
  return true;
}

int Options::get (const char * name) {
  Option * o = has (name);
  return o ? o->val (this) : 0;
}

/*------------------------------------------------------------------------*/

void Options::print () {
  unsigned different = 0;
#ifdef QUIET
  const bool verbose = false;
#endif
  char buffer[160];
  // We prefer the macro iteration here since '[VLH]' might be '1e9' etc.
#define OPTION(N,V,L,H,O,D) \
  if (N != (V)) different++; \
  if (verbose || N != (V)) { \
    if ((L) == 0 && (H) == 1) { \
      sprintf (buffer, "--" #N "=%s", (N ? "true" : "false")); \
      MSG ("  %s%-30s%s (%s default %s'%s'%s)", \
        ((N == (V)) ? "" : tout.bright_yellow_code ()), \
        buffer, \
        ((N == (V)) ? "" : tout.normal_code ()), \
        ((N == (V)) ? "same as" : "different from"), \
        ((N == (V)) ? tout.green_code () : tout.yellow_code ()), \
        (bool)(V) ? "true" : "false", \
        tout.normal_code ()); \
    } else { \
      sprintf (buffer, "--" #N "=%d", N); \
      MSG ("  %s%-30s%s (%s default %s'" #V "'%s)", \
        ((N == (V)) ? "" : tout.bright_yellow_code ()), \
        buffer, \
        ((N == (V)) ? "" : tout.normal_code ()), \
        ((N == (V)) ? "same as" : "different from"), \
        ((N == (V)) ? tout.green_code () : tout.yellow_code ()), \
        tout.normal_code ()); \
    } \
  }
  OPTIONS
#undef OPTION
  if (!different) MSG ("all options are set to their default value");
}

/*------------------------------------------------------------------------*/

void Options::usage () {
  // We prefer the macro iteration here since '[VLH]' might be '1e9' etc.
#define OPTION(N,V,L,H,O,D) \
  if ((L) == 0 && (H) == 1) \
    printf ("  %-26s " D " [%s]\n", \
      "--" #N "=bool", (bool)(V) ? "true" : "false"); \
  else \
    printf ("  %-26s " D " [" #V "]\n", \
      "--" #N "=" #L ".." #H);
  OPTIONS
#undef OPTION
}

/*------------------------------------------------------------------------*/

void Options::optimize (int val) {

  if (val < 0) {
    LOG ("ignoring negative optimization mode '%d'", val);
    return;
  }

  const int max_val = 3;
  if (val > max_val) {
    LOG ("optimization argument '%d' reduced to '%d'", val, max_val);
    val = max_val;
  }

  int64_t factor;
  switch (val) {
    default: factor = 1; break;
    case 1: factor = 10; break;
    case 2: factor = 100; break;
    case 3: factor = 1e9; break;
  }
  int increased = 0;
#define OPTION(N,V,L,H,O,D) \
  do { \
    if (!(O)) break; \
    int64_t new_val = factor * (int64_t) (V); \
    if (new_val > (H)) new_val = (H); \
    if (new_val == (int) (V)) break; \
    LOG ("optimization mode '%d' for '%s' " \
      "gives '%" PRId64 "' instead of '%d", \
      val, #N, new_val, (int) (V)); \
    assert (new_val <= INT_MAX); \
    N = (int) new_val; \
    increased++; \
  } while (0);
  OPTIONS
#undef OPTION
  if (increased)
    MSG ("optimization mode '-O%d' increased %d limits by '%" PRId64 "'",
      val, increased, factor);

  switch (val) {
    default: factor = 1; break;
    case 1: factor = 2; break;
    case 2: factor = 4; break;
    case 3: factor = 1024; break;
  }
  increased = 0;
#define OPTION(N,V,L,H,O,D) \
  do { \
    if (!has_suffix (#N, "rounds")) break; \
    int64_t new_val = factor * (int64_t) (V); \
    if (new_val > (H)) new_val = (H); \
    if (new_val == (int) (V)) break; \
    LOG ("optimization mode '%d' for '%s' " \
      "gives '%" PRId64 "' instead of '%d", \
      val, #N, new_val, (int) (V)); \
    assert (new_val <= INT_MAX); \
    N = (int) new_val; \
    increased++; \
  } while (0);
  OPTIONS
#undef OPTION
  if (increased)
    MSG ("optimization mode '-O%d' increased %d limits by '%" PRId64 "'",
      val, increased, factor);
}

/*------------------------------------------------------------------------*/

}
