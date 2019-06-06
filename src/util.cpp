#include "internal.hpp"

namespace CaDiCaL {

bool parse_int_str (const char * str, int & res) {
  const char * p = str;
  int sign, ch;
  if ((ch = *p++) == '-') {
    sign = -1;
    if ((ch = *p++) == '0') return false;
  } else sign = 1;
  if (!isdigit (ch)) return false;
  int64_t tmp = ch - '0';
  while (isdigit (ch = *p++)) {
    tmp = 10 * tmp + (ch - '0');
    if (tmp > -(int64_t)INT_MIN) return false;
  }
  if (ch) return false;
  tmp *= sign;
  if (tmp < (int64_t) INT_MIN) return false;
  if (tmp > (int64_t) INT_MAX) return false;
  res = tmp;
  return true;
}

bool has_suffix (const char * str, const char * suffix) {
  size_t k = strlen (str), l = strlen (suffix);
  return k > l && !strcmp (str + k - l, suffix);
}

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
