#ifndef _error_hpp_INCLUDED
#define _error_hpp_INCLUDED

#define ERROR_START(FMT,ARGS...) \
do { \
  fflush (stdout); \
  fputs ("*** 'CaDiCaL' error: ", stderr); \
  fprintf (stderr, FMT, ##ARGS); \
} while (0)

#define ERROR_END() \
do { \
  fputc ('\n', stderr); \
  fflush (stderr); \
  abort (); \
} while (0)

#define ERROR(FMT,ARGS...) \
do { \
  ERROR_START (FMT,##ARGS); \
  ERROR_END (fmt); \
} while (0)

#endif
