#ifndef _macros_hpp_INCLUDED
#define _macros_hpp_INCLUDED

// Central file for keeping (most) macros.

/*------------------------------------------------------------------------*/

#define START(P) \
do { \
  if (internal->profiles.P.level > internal->opts.profile) break; \
  internal->start_profiling (&internal->profiles.P); \
} while (0)

#define STOP(P) \
do { \
  if (internal->profiles.P.level > internal->opts.profile) break; \
  internal->stop_profiling (&internal->profiles.P); \
} while (0)

/*------------------------------------------------------------------------*/

#define NEW(P,T,N) \
do { (P) = new T[N], internal->inc_bytes ((N) * sizeof (T)); } while (0)

#define RESIZE(P,T,O,N) \
do { \
  T * TMP = (P); \
  NEW (P, T, N); \
  for (size_t I = 0; I < (O); I++) (P)[I] = (TMP)[I]; \
  internal->dec_bytes ((O) * sizeof (T)); \
  delete [] TMP; \
} while (0)

/*------------------------------------------------------------------------*/

#define MSG(ARGS...) \
do { Message::print (internal, 0, ##ARGS); } while (0)

#define VRB(ARGS...) \
do { Message::print (internal, 1, ##ARGS); } while (0)

#define SECTION(ARGS...) \
do { Message::section (internal, ##ARGS); } while (0)

/*------------------------------------------------------------------------*/

#define UPDATE_AVG(EMA_OR_AVG,Y) \
do { EMA_OR_AVG.update (internal, (Y), #EMA_OR_AVG); } while (0)

#define INIT_EMA(E,V) \
  E = EMA (V); \
  LOG ("init " #E " EMA target alpha %g", (double) V)

#endif
