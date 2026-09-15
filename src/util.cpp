#include "util.hpp"
#include "internal.hpp"
#include <cstdint>
#include <limits>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

bool parse_int_str (const char *str, int &val) {
  int64_t parsed;
  if (!parse_int_str (str, parsed))
    return false;

  if (parsed < INT_MIN)
    parsed = INT_MIN;
  else if (parsed > INT_MAX)
    parsed = INT_MAX;

  val = static_cast<int> (parsed);
  return true;
}

bool parse_int_str (const char *val_str, int64_t &val) {
  if (!strcmp (val_str, "true"))
    val = 1;
  else if (!strcmp (val_str, "false"))
    val = 0;
  else {
    const char *p = val_str;
    int sign;

    if (*p == '-')
      sign = -1, p++;
    else
      sign = 1;

    int ch;
    if (!isdigit ((ch = *p++)))
      return false;

    const uint64_t bound =
        static_cast<uint64_t> (std::numeric_limits<int64_t>::max ()) + 1;
    uint64_t mantissa = ch - '0';

    while (isdigit (ch = *p++)) {
      if (bound / 10 < mantissa)
        mantissa = bound;
      else
        mantissa *= 10;
      const int digit = ch - '0';
      if (bound - digit < mantissa)
        mantissa = bound;
      else
        mantissa += digit;
    }

    int exponent = 0;
    if (ch == 'e') {
      while (isdigit ((ch = *p++)))
        exponent = exponent ? 10 : ch - '0';
      if (ch)
        return false;
    } else if (ch)
      return false;

    assert (exponent <= 10);
    uint64_t val_u64 = mantissa;
    for (int i = 0; i < exponent; i++) {
      if (val_u64 > bound / 10)
        val_u64 = bound;
      else
        val_u64 *= 10;
    }

    int64_t val64;
    if (sign < 0) {
      if (val_u64 >= bound) {
        val64 = std::numeric_limits<int64_t>::min ();
      } else {
        val64 = -static_cast<int64_t> (val_u64);
      }
    } else {
      if (val_u64 >= bound) {
        val64 = std::numeric_limits<int64_t>::max ();
      } else {
        val64 = val_u64;
      }
    }

    val = val64;
  }
  return true;
}

/*------------------------------------------------------------------------*/

bool has_suffix (const char *str, const char *suffix) {
  size_t k = strlen (str), l = strlen (suffix);
  return k > l && !strcmp (str + k - l, suffix);
}

bool has_prefix (const char *str, const char *prefix) {
  for (const char *p = str, *q = prefix; *q; q++, p++)
    if (*q != *p)
      return false;
  return true;
}

/*------------------------------------------------------------------------*/

bool is_color_option (const char *arg) {
  return !strcmp (arg, "--color") || !strcmp (arg, "--colors") ||
         !strcmp (arg, "--colour") || !strcmp (arg, "--colours") ||
         !strcmp (arg, "--color=1") || !strcmp (arg, "--colors=1") ||
         !strcmp (arg, "--colour=1") || !strcmp (arg, "--colours=1") ||
         !strcmp (arg, "--color=true") || !strcmp (arg, "--colors=true") ||
         !strcmp (arg, "--colour=true") || !strcmp (arg, "--colours=true");
}

bool is_no_color_option (const char *arg) {
  return !strcmp (arg, "--no-color") || !strcmp (arg, "--no-colors") ||
         !strcmp (arg, "--no-colour") || !strcmp (arg, "--no-colours") ||
         !strcmp (arg, "--color=0") || !strcmp (arg, "--colors=0") ||
         !strcmp (arg, "--colour=0") || !strcmp (arg, "--colours=0") ||
         !strcmp (arg, "--color=false") ||
         !strcmp (arg, "--colors=false") ||
         !strcmp (arg, "--colour=false") ||
         !strcmp (arg, "--colours=false");
}

/*------------------------------------------------------------------------*/

static uint64_t primes[] = {
    1111111111111111111lu, 2222222222222222249lu, 3333333333333333347lu,
    4444444444444444537lu, 5555555555555555621lu, 6666666666666666677lu,
    7777777777777777793lu, 8888888888888888923lu, 9999999999999999961lu,
};

uint64_t hash_string (const char *str) {
  const unsigned size = sizeof primes / sizeof *primes;
  uint64_t res = 0;
  unsigned char ch;
  unsigned i = 0;
  for (const char *p = str; (ch = *p); p++) {
    res += ch;
    res *= primes[i++];
    if (i == size)
      i = 0;
  }
  return res;
}

} // namespace CaDiCaL
