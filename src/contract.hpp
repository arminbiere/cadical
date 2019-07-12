#ifndef _contract_hpp_INCLUDED
#define _contract_hpp_INCLUDED

/*------------------------------------------------------------------------*/

// If the user violates API contracts while calling functions declared in
// 'cadical.hpp' and implemented in 'solver.cpp' then an error is reported.
// Currently we also force aborting the program.  In the future it might be
// better to allow the user to provide a call back function, which then can
// for instance throw a C++ exception or execute a 'longjmp' in 'C' etc.

#define CONTRACT_VIOLATED(...) \
do { \
  Internal::fatal_message_start (); \
  fprintf (stderr, \
    "invalid API usage of '%s' in '%s': ", \
    __PRETTY_FUNCTION__, __FILE__); \
  fprintf (stderr, __VA_ARGS__); \
  fputc ('\n', stderr); \
  fflush (stderr); \
  abort (); \
} while (0)

/*------------------------------------------------------------------------*/

// These are common shortcuts for 'Solver' API contracts (requirements).

#define REQUIRE(COND,...) \
do { \
  if ((COND)) break; \
  CONTRACT_VIOLATED (__VA_ARGS__); \
} while (0)

#define REQUIRE_INITIALIZED() \
do { \
  REQUIRE(this != 0, "solver not initialized"); \
  REQUIRE(external != 0, "internal solver not initialized"); \
  REQUIRE(internal != 0, "internal solver not initialized"); \
} while (0)

#define REQUIRE_VALID_STATE() \
do { \
  REQUIRE_INITIALIZED (); \
  REQUIRE(this->state () & VALID, "solver in invalid state"); \
} while (0)

#define REQUIRE_VALID_OR_SOLVING_STATE() \
do { \
  REQUIRE_INITIALIZED (); \
  REQUIRE(this->state () & (VALID | SOLVING), \
    "solver neither in valid nor solving state"); \
} while (0)

#define REQUIRE_VALID_LIT(LIT) \
do { \
  REQUIRE ((int)(LIT) && ((int) (LIT)) != INT_MIN, \
    "invalid literal '%d'", (int)(LIT)); \
} while (0)

/*------------------------------------------------------------------------*/

#endif
