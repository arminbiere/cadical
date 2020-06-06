#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

bool parse_int_str(const char * val_str, int & val)
{
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

/*------------------------------------------------------------------------*/

bool has_suffix (const char * str, const char * suffix) {
  size_t k = strlen (str), l = strlen (suffix);
  return k > l && !strcmp (str + k - l, suffix);
}

bool has_prefix (const char * str, const char * prefix) {
  for (const char * p = str, * q = prefix; *q; q++, p++)
    if (*q != *p)
      return false;
  return true;
}

/*------------------------------------------------------------------------*/

bool is_color_option (const char * arg) {
  return !strcmp (arg, "--color") ||
         !strcmp (arg, "--colors") ||
         !strcmp (arg, "--colour") ||
         !strcmp (arg, "--colours") ||
         !strcmp (arg, "--color=1") ||
         !strcmp (arg, "--colors=1") ||
         !strcmp (arg, "--colour=1") ||
         !strcmp (arg, "--colours=1") ||
         !strcmp (arg, "--color=true") ||
         !strcmp (arg, "--colors=true") ||
         !strcmp (arg, "--colour=true") ||
         !strcmp (arg, "--colours=true");
}

bool is_no_color_option (const char * arg) {
  return !strcmp (arg, "--no-color") ||
         !strcmp (arg, "--no-colors") ||
         !strcmp (arg, "--no-colour") ||
         !strcmp (arg, "--no-colours") ||
         !strcmp (arg, "--color=0") ||
         !strcmp (arg, "--colors=0") ||
         !strcmp (arg, "--colour=0") ||
         !strcmp (arg, "--colours=0") ||
         !strcmp (arg, "--color=false") ||
         !strcmp (arg, "--colors=false") ||
         !strcmp (arg, "--colour=false") ||
         !strcmp (arg, "--colours=false");
}

}
