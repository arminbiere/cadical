#ifndef _util_hpp_INCLUDED
#define _util_hpp_INCLUDED

namespace CaDiCaL {

using namespace std;

// Common simple utility functions independent from 'Internal'.

/*------------------------------------------------------------------------*/

inline double relative (double a, double b) { return b ? a / b : 0; }
inline double percent (double a, double b) { return relative (100 * a, b); }
inline int sign (int lit) { return (lit > 0) - (lit < 0); }

/*------------------------------------------------------------------------*/

bool is_int_str (const char * str);
bool is_double_str (const char * str);
bool has_suffix (const char * str, const char * suffix);

/*------------------------------------------------------------------------*/

inline unsigned next_power_of_two (unsigned n) {
  return 1u << (32 - __builtin_clz (n - 1));
}

inline bool is_power_of_two (unsigned n) {
  return n && !(n & (n-1));
}

/*------------------------------------------------------------------------*/

inline bool aligned (size_t bytes, size_t alignment) {
  assert (is_power_of_two (alignment));
  return !(bytes & (alignment - 1));
}

inline bool aligned (void * ptr, size_t alignment) {
  return aligned ((size_t) ptr, alignment);
}

inline size_t align (size_t bytes, size_t alignment) {
  assert (is_power_of_two (alignment));
  if (aligned (bytes, alignment)) return bytes;
  else return (bytes | (alignment - 1)) + 1;
}

/*------------------------------------------------------------------------*/

// The standard 'Effective STL' way (though not guaranteed) to clear a
// vector and reduce its capacity to zero, thus deallocating all its
// internal memory.  This is quite important for keeping the actual
// allocated size of watched and occurrence lists small particularly during
// bounded variable elimination where many clauses are added and removed.

template<class T> void erase_vector (vector<T> & v) {
  if (v.capacity ()) { vector<T>().swap (v); }
  assert (!v.capacity ());                          // not guaranteed though
}

// The standard 'Effective STL' way (though not guaranteed) to shrink the
// capacity of a vector to its size thus kind of releasing all the internal
// excess memory not needed at the moment any more.

template<class T> void shrink_vector (vector<T> & v) {
  if (v.capacity () > v.size ()) { vector<T>(v).swap (v); }
  assert (v.capacity () == v.size ());              // not guaranteed though
}

/*------------------------------------------------------------------------*/

};

#endif
