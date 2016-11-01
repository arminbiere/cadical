#include "util.hpp"

#include <cctype>

namespace CaDiCaL {

bool is_int_str (const char * str) {
  const char * p = str;
  if (!*p) return false;
  if ((*p == '-' || *p == '+') && !(*++p)) return false;
  if (!isdigit (*p++)) return false;
  while (isdigit (*p)) p++;
  return !*p;
}

bool is_double_str (const char * str) {
  const char * p = str;
  if (!*p) return false;
  if ((*p == '-' || *p == '+') && !(*++p)) return false;
  while (isdigit (*p)) p++;
  if (*p == '.') p++;
  while (isdigit (*p)) p++;
  if (*p == 'e') {
    p++;
    if ((*p == '-' || *p == '+') && !(*++p)) return false;
    while (isdigit (*p)) p++;
  }
  return !*p;
}

};
