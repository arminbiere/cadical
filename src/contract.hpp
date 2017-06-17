#ifndef _contract_hpp_INCLUDED
#define _contract_hpp_INCLUDED

#define CONTRACT_VIOLATED(FMT,ARGS...) \
do { \
  fflush (stdout); \
  fprintf (stderr, \
    "*** 'CaDiCaL' invalid API usage of '%s' in '%s': ", \
    __FUNCTION__, __FILE__); \
  fprintf (stderr, FMT, ##ARGS); \
  fputc ('\n', stderr); \
  abort (); \
} while (0)

#define INITIALIZED() \
do { \
  if (this) break; \
  CONTRACT_VIOLATED ("uninitialized"); \
} while (0)

#define REQUIRE(COND,FMT,ARGS...) \
do { \
  INITIALIZED (); \
  if ((COND)) break; \
  CONTRACT_VIOLATED (FMT, ##ARGS); \
} while (0)

#endif
