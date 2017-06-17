#ifndef _contract_hpp_INCLUDED
#define _contract_hpp_INCLUDED

#define CONTRACT_VIOLATED(FMT,ARGS...) \
do { \
  fflush (stdout); \
  fprintf (stderr, \
    "*** 'CaDiCaL' invalid API usage of '%s' in '%s': ", \
    __PRETTY_FUNCTION__, __FILE__); \
  fprintf (stderr, FMT, ##ARGS); \
  fputc ('\n', stderr); \
  raise (CaDiCaL::Solver::contract_violation_signal); \
  abort (); \
} while (0)

#define REQUIRE(COND,FMT,ARGS...) \
do { \
  if ((COND)) break; \
  CONTRACT_VIOLATED (FMT, ##ARGS); \
} while (0)

#define REQUIRE_INITIALIZED() \
do { \
  REQUIRE(this, "solver uninitialized"); \
} while (0)

#define REQUIRE_VALID_LIT(LIT) \
do { \
  REQUIRE ((((int) (LIT)) != INT_MIN), \
    "invalid literal '%ld'", (long)(LIT)); \
} while (0)

#endif
