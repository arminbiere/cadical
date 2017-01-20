#ifndef _macros_hpp_INCLUDED
#define _macros_hpp_INCLUDED

/*------------------------------------------------------------------------*/

// Central file for keeping (most) macros.

/*------------------------------------------------------------------------*/

// Profiling support.

#ifndef QUIET

#define START(P,ARGS...) \
do { \
  if (internal->profiles.P.level > internal->opts.profile) break; \
  internal->start_profiling (&internal->profiles.P, ##ARGS); \
} while (0)

#define STOP(P,ARGS...) \
do { \
  if (internal->profiles.P.level > internal->opts.profile) break; \
  internal->stop_profiling (&internal->profiles.P, ##ARGS); \
} while (0)

#define SWITCH_AND_START(F,T,P) \
do { \
  const double N = process_time (); \
  const int L = internal->opts.profile; \
  if (internal->profiles.F.level <= L)  STOP (F, N); \
  if (internal->profiles.T.level <= L) START (T, N); \
  if (internal->profiles.P.level <= L) START (P, N); \
} while (0)

#define STOP_AND_SWITCH(P,F,T) \
do { \
  const double N = process_time (); \
  const int L = internal->opts.profile; \
  if (internal->profiles.P.level <= L)  STOP (P, N); \
  if (internal->profiles.F.level <= L)  STOP (F, N); \
  if (internal->profiles.T.level <= L) START (T, N); \
} while (0)

#else // ifndef QUIET

#define START(ARGS...) do { } while (0)
#define STOP(ARGS...) do { } while (0)

#define SWITCH_AND_START(ARGS...) do { } while (0)
#define STOP_AND_SWITCH(ARGS...) do { } while (0)

#endif

/*------------------------------------------------------------------------*/

// Compact message code.

#ifndef QUIET

#define MSG(ARGS...) Message::message (internal, ##ARGS)
#define VRB(ARGS...) Message::verbose (internal, ##ARGS)
#define SECTION(ARGS...) Message::section (internal, ##ARGS)

#else

#define MSG(ARGS...) do { } while (0)
#define VRB(ARGS...) do { } while (0)
#define SECTION(ARGS...) do { } while (0)

#endif

// Parse error.

#define PER(FMT,ARGS...) \
do { \
  internal->error.init (\
    "%s:%d: parse error: ", \
    file->name (), (int) file->lineno ()); \
  return internal->error.append (FMT, ##ARGS); \
} while (0)

/*------------------------------------------------------------------------*/

// Compact average update and initialization code for better logging.

#define UPDATE_AVERAGE(A,Y) \
do { A.update (internal, (Y), #A); } while (0)

#define INIT_EMA(E,V) \
  E = EMA (V); \
  LOG ("init " #E " EMA target alpha %g", (double) V)

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

#endif
