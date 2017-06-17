#ifndef _cover_hpp_INCLUDED
#define _cover_hpp_INCLUDED

/*------------------------------------------------------------------------*/

// Coverage goal, used similar to 'assert' (but with flipped condition) and
// also included even if 'NDEBUG' is defined (in optimizing compilation).

#define COVER(COND) \
do { \
  if (!(COND)) break; \
  fprintf (stderr, \
    "libcadical.a: %s:%d: %s: Coverage target `%s' reached.\n", \
    __FUNCTION__, __LINE__, __FILE__, # COND); \
  fflush (stderr); \
  abort (); \
} while (0)

/*------------------------------------------------------------------------*/

#endif
