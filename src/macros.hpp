#ifndef _macros_hpp_INCLUDED
#define _macros_hpp_INCLUDED

/*------------------------------------------------------------------------*/

// Central file for keeping (most) macros.

/*------------------------------------------------------------------------*/

// Profiling support.

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
  const double N = seconds (); \
  const int L = internal->opts.profile; \
  if (internal->profiles.F.level <= L)  STOP (F, N); \
  if (internal->profiles.T.level <= L) START (T, N); \
  if (internal->profiles.P.level <= L) START (P, N); \
} while (0)

#define STOP_AND_SWITCH(P,F,T) \
do { \
  const double N = seconds (); \
  const int L = internal->opts.profile; \
  if (internal->profiles.P.level <= L)  STOP (P, N); \
  if (internal->profiles.F.level <= L)  STOP (F, N); \
  if (internal->profiles.T.level <= L) START (T, N); \
} while (0)

/*------------------------------------------------------------------------*/

// Memory allocation with implicit memory usage updates.

#define NEW(P,T,N) \
do { (P) = new T[N], internal->inc_bytes ((N) * sizeof (T)); } while (0)

#define DEL(P,T,N) \
do { delete [] (P), internal->dec_bytes ((N) * sizeof (T)); } while (0)

#define ZERO(P,T,N) \
do { memset ((P), 0, (N) * sizeof (T)); } while (0)

#define ENLARGE(P,T,O,N) \
do { \
  T * TMP = (P); \
  NEW (P, T, N); \
  for (size_t I = 0; I < (O); I++) (P)[I] = (TMP)[I]; \
  internal->dec_bytes ((O) * sizeof (T)); \
  delete [] TMP; \
} while (0)

/*------------------------------------------------------------------------*/

// Compact message code.

#define MSG(ARGS...) Message::message (internal, ##ARGS)
#define VRB(ARGS...) Message::verbose (internal, ##ARGS)
#define SECTION(ARGS...) Message::section (internal, ##ARGS)

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

#define UPDATE_AVG(EMA_OR_AVG,Y) \
do { EMA_OR_AVG.update (internal, (Y), #EMA_OR_AVG); } while (0)

#define INIT_EMA(E,V) \
  E = EMA (V); \
  LOG ("init " #E " EMA target alpha %g", (double) V)

#endif
