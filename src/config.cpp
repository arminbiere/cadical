#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

struct NameVal { const char * name; int val; };

static NameVal sat_config[] = {
  { "elimreleff", 10 },
  { "stabilizeonly", 1 },
  { "subsumereleff", 60 },
};

static NameVal unsat_config[] = {
  { "stabilize", 0 },
  { "walk", 0 },
};

/*------------------------------------------------------------------------*/

#define CONFIGS \
 \
CONFIG(sat,"target satisfiable instances") \
CONFIG(unsat,"target unsatisfiable instances") \

/*------------------------------------------------------------------------*/

bool Config::has (const char * name) {
  if (!strcmp (name, "default")) return true;
#define CONFIG(N,D) \
  if (!strcmp (name, #N)) return true;
  CONFIGS
#undef CONFIG
  return false;
}

bool Config::set (Solver & solver, const char * name) {
  if (!strcmp (name, "default")) return true;
#define CONFIG(N,D) \
  do { \
    if (strcmp (name, #N)) break; \
    const NameVal * BEGIN = N ## _config; \
    const NameVal * END = BEGIN + sizeof N ##_config / sizeof (NameVal); \
    for (const NameVal * P = BEGIN; P != END; P++) { \
      assert (solver.is_valid_option (P->name)); \
      solver.set (P->name, P->val); \
    } \
    return true; \
  } while (0);
  CONFIGS
#undef CONFIG
  return false;
}

const char * Config::description (const char * name) {
  if (!strcmp (name, "default"))
    return "should work in most situations";
#define CONFIG(N,D) \
  if (!strcmp (name, #N)) return D;
  CONFIGS
#undef CONFIG
  return 0;
}

void Config::usage () {
#define CONFIG(N,D) \
  printf ("  %-26s " D "\n", "--" #N);
  CONFIGS
#undef CONFIG
}

}
