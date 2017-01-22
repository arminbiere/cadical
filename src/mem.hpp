#ifndef _mem_hpp_INCLUDED
#define _mem_hpp_INCLUDED

// Memory allocation.

#define NEW(P,T,N) \
do { (P) = new T[N]; } while (0)

#define DELETE(P,T,N) \
do { delete [] (P); } while (0)

#define ZERO(P,T,N) \
do { memset ((P), 0, (N) * sizeof (T)); } while (0)

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

#endif
