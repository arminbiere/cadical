#ifndef _mem_hpp_INCLUDED
#define _mem_hpp_INCLUDED

// Memory allocation.

/*------------------------------------------------------------------------*/

#define ZERO(P,T,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  memset (P, 0, (N) * sizeof (T)); \
} while (0)

/*------------------------------------------------------------------------*/
#ifdef NREALLOC // do not use no C style 'realloc' for any tables
/*------------------------------------------------------------------------*/

// C++ allocators are wastefull during shrinking memory blocks for variables
// in 'compact'. They can not make use of implicit zero initialization as
// with 'ccmalloc' nor memory reuse as with 'realloc'.

#define NEW_ONLY(P,T,N) \
do { \
  (P) = new T[N]; \
} while (0) 

#define NEW_ZERO(P,T,N) \
do { \
  NEW_ONLY (P, T, N); \
  ZERO (P, T, N); \
} while (0) 

#define RELEASE_DELETE(P,T,N) \
do { delete [] (P); } while (0)

#define DELETE_ONLY RELEASE_DELETE

#define ENLARGE_ONLY(P,T,O,N) \
do { \
  assert ((O) <= (N)); \
  if ((O) == (N)) break; \
  T * TMP = P; \
  NEW_ONLY (P, T, N); \
  for (size_t I = 0; I < (O); I++) P[I] = TMP[I]; \
  delete [] TMP; \
} while (0)

#define ENLARGE_ZERO(P,T,O,N) \
do { \
  ENLARGE_ONLY (P, T, O, N); \
  ZERO (P + O, T, N - O); \
} while (0)

#define RELEASE_SHRINK(P,T,O,N) \
do { \
  assert ((O) >= (N)); \
  if ((O) == (N)) break; \
  T * TMP = (P); \
  NEW_ZERO (P, T, N); \
  for (size_t I = 0; I < (N); I++) P[I] = TMP[I]; \
  delete [] TMP; \
} while (0)

#define SHRINK_ONLY RELEASE_SHRINK

/*------------------------------------------------------------------------*/
#else // #ifdef NREALLOC
/*------------------------------------------------------------------------*/

// C allocators which can make use of 'calloc' & 'realloc'.  The former
// 'calloc' allows allocation of implicit zero initialized memory (our tests
// suggest that the 'ccmalloc' implementation in Linux uses the same amount
// of resident set size as 'malloc', but zero initialization on demand).
// Similarly 'realloc' allows to really shrink an allocated memory in place.
// This can save up-to half the memory w.r.t. resident size for those
// blocks.  The largest allocated continous blocks are those containing C++
// 'std::vector' objects ('wtab', 'big').  For those we carefully have to
// copy their internal data structures and also release them.  Our code
// assumes that zero initialized memory for a 'std::vector' is fine.

#define NEW_ONLY(P,T,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  (P) = (T *) malloc ((N) * sizeof (T)); \
  if (!(P)) throw bad_alloc (); \
} while (0)

#define NEW_ZERO(P,T,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  (P) = (T *) calloc ((N), sizeof (T)); \
  if (!(P)) throw bad_alloc (); \
} while (0)

#define RELEASE_DELETE(P,T,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  for (size_t I = 0; I < (size_t) (N); I++) T().swap (P[I]); \
  free ((P)); \
} while (0)

#define DELETE_ONLY(P,T,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  free ((P)); \
} while (0)

#define ENLARGE_ONLY(P,T,O,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  if ((O) == (N)) break; \
  assert ((O) < (N)); \
  (P) = (T *) realloc ((P), (N) * sizeof (T)); \
  if ((N) && !(P)) throw bad_alloc (); \
} while (0)

#define ENLARGE_ZERO(P,T,O,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  if ((O) == (N)) break; \
  assert ((O) < (N)); \
  if (!(O)) NEW_ZERO (P, T, N); /* 'calloc' is preferred */ \
  else { \
    (P) = (T *) realloc ((P), (N) * sizeof (T)); \
    if (!(P)) throw bad_alloc (); \
    ZERO ((P) + (O), T, (N) - (O)); \
  } \
} while (0)

#define RELEASE_SHRINK(P,T,O,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  if ((O) == (N)) break; \
  assert ((N) < (O)); \
  for (size_t I = (size_t) N; I < (size_t) (O); I++) T().swap (P[I]); \
  (P) = (T *) realloc ((P), (N) * sizeof (T)); \
  if ((N) && !(P)) throw bad_alloc (); \
} while (0)

#define SHRINK_ONLY(P,T,O,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  if ((O) == (N)) break; \
  assert ((N) < (O)); \
  (P) = (T *) realloc ((P), (N) * sizeof (T)); \
  if ((N) && !(P)) throw bad_alloc (); \
} while (0)

/*------------------------------------------------------------------------*/
#endif // #ifdef NREALLOC
/*------------------------------------------------------------------------*/

#endif // ifndef _mem_hpp_INCLUDED
