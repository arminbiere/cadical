#ifndef _macros_hpp_INCLUDED
#define _macros_hpp_INCLUDED

// Central file for keeping (most) macros.

/*------------------------------------------------------------------------*/

#define START(P) \
do { \
  if (solver->profiles.P.level > solver->opts.profile) break; \
  solver->start_profiling (&solver->profiles.P); \
} while (0)

#define STOP(P) \
do { \
  if (solver->profiles.P.level > solver->opts.profile) break; \
  solver->stop_profiling (&solver->profiles.P); \
} while (0)

/*------------------------------------------------------------------------*/

#define NEW(P,T,N) \
  do { (P) = new T[N], solver->inc_bytes ((N) * sizeof (T)); } while (0)

/*------------------------------------------------------------------------*/

#define MSG(ARGS...) \
do { Message::print (solver, 0, ##ARGS); } while (0)

#define VRB(ARGS...) \
do { Message::print (solver, 1, ##ARGS); } while (0)

#define DIE(ARGS...) \
do { Message::die (solver, ##ARGS); } while (0)

#define PER(ARGS...) \
do { Message::parse_error (solver, file, ##ARGS); } while (0)

#define SECTION(ARGS...) \
do { Message::section (solver, ##ARGS); } while (0)

/*------------------------------------------------------------------------*/

#define UPDATE_AVG(EMA_OR_AVG,Y) \
do { EMA_OR_AVG.update (solver, (Y), #EMA_OR_AVG); } while (0)

#define INIT_EMA(E,V) \
  E = EMA (V); \
  LOG ("init " #E " EMA target alpha %g", (double) V)

#endif
