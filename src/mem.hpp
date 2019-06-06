#ifndef _mem_hpp_INCLUDED
#define _mem_hpp_INCLUDED

// Memory allocation.

/*------------------------------------------------------------------------*/

#define ZERO(P,T,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  memset ((void*) (P), 0, (N) * sizeof (T)); \
} while (0)

/*------------------------------------------------------------------------*/

// We often use C style memory allocation so that we can make use of
// 'calloc' & 'realloc'.  The former 'calloc' allows allocation of implicit
// zero initialized memory (our tests suggest that the 'calloc'
// implementation in Linux uses the same amount of resident set size as
// 'malloc', but zero initialization on demand).  Similarly 'realloc' allows
// to really shrink an allocated memory in place.  This can save up to half
// the memory in terms of resident size for those blocks.  The largest
// allocated contiguous blocks are those containing C++ 'std::vector'
// objects ('wtab', 'big').  For those we carefully have to copy their
// internal data structures and also release them.  Our code assumes that
// zero initialized memory for a 'std::vector' is fine.

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
  (P) = (T *) realloc ((void*)(P), (N) * sizeof (T)); \
  if ((N) != 0 && (P) == 0) throw bad_alloc (); \
} while (0)

#define ENLARGE_ZERO(P,T,O,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  if ((O) == (N)) break; \
  assert ((O) < (N)); \
  if ((O) == 0) NEW_ZERO (P, T, N); /* 'calloc' is preferred */ \
  else { \
    (P) = (T *) realloc ((void*)(P), (N) * sizeof (T)); \
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
  (P) = (T *) realloc ((void*)(P), (N) * sizeof (T)); \
  if ((N) != 0 && (P) == 0) throw bad_alloc (); \
} while (0)

#define SHRINK_ONLY(P,T,O,N) \
do { \
  assert (sizeof (T) == sizeof *(P)); \
  if ((O) == (N)) break; \
  assert ((N) < (O)); \
  (P) = (T *) realloc ((P), (N) * sizeof (T)); \
  if ((N) != 0 && (P) == 0) throw bad_alloc (); \
} while (0)

/*------------------------------------------------------------------------*/

#endif // ifndef _mem_hpp_INCLUDED
