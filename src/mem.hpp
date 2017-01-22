#ifndef _mem_hpp_INCLUDED
#define _mem_hpp_INCLUDED

// Memory allocation.

#define ZERO(P,T,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  memset ((P), 0, (N) * sizeof (T)); \
} while (0)

#if 0

#define NEW(P,T,N) \
do { (P) = new T[N]; } while (0)

#define DELETE(P,T,N) \
do { delete [] (P); } while (0)

#define ENLARGE(P,T,O,N) \
do { \
  assert ((O) <= (N)); \
  if ((O) == (N)) break; \
  T * TMP = (P); \
  NEW (P, T, N); \
  for (size_t I = 0; I < (O); I++) (P)[I] = (TMP)[I]; \
  delete [] TMP; \
} while (0)

#define SHRINK(P,T,O,N) \
do { \
  assert ((O) >= (N)); \
  if ((O) == (N)) break; \
  T * TMP = (P); \
  NEW (P, T, N); \
  for (size_t I = 0; I < (N); I++) (P)[I] = (TMP)[I]; \
  delete [] TMP; \
} while (0)

#else

#define NEW(P,T,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  (P) = (T *) calloc ((N), sizeof (T)); \
  if (!(P)) throw bad_alloc (); \
} while (0)

#define DELETE(P,T,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  for (size_t I = 0; I < (size_t) (N); I++) (P)[I] = T(); \
  free ((P)); \
} while (0)

#define ENLARGE(P,T,O,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  if ((O) == (N)) break; \
  assert ((O) < (N)); \
  (P) = (T *) realloc ((P), (N) * sizeof (T)); \
  if (!(P)) throw bad_alloc (); \
  ZERO ((P) + (O), T, (N) - (O)); \
} while (0)

#define SHRINK(P,T,O,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  if ((O) == (N)) break; \
  assert ((N) < (O)); \
  for (size_t I = (size_t) N; I < (size_t) (O); I++) (P)[I] = T(); \
  (P) = (T *) realloc ((P), (N) * sizeof (T)); \
  if ((N) && !(P)) throw bad_alloc (); \
} while (0)

#endif // if 0
#endif // ifndef _mem_hpp_INCLUDED
