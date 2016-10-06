#ifndef _macros_hpp_INCLUDED
#define _macros_hpp_INCLUDED

#ifdef PROFILING
#define START(P) solver->start_profiling (&solver->profiles.P)
#define STOP(P) solver->stop_profiling (&solver->profiles.P)
#else
#define START(P) do { } while (0)
#define STOP(P) do { } while (0)
#endif

#define NEW(P,T,N) \
  do { (P) = new T[N], solver->inc_bytes ((N) * sizeof (T)); } while (0)

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

#define UPDATE(EMA_OR_AVG,Y) EMA_OR_AVG.update ((Y), #EMA_OR_AVG)

#endif
