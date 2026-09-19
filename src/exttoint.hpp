#ifndef _exttoint_hpp_INCLUDED
#define _exttoint_hpp_INCLUDED

#include "hashmap.hpp"
#include "util.hpp"
#include <limits>

#undef MYPRINTF
#ifdef MYPRINTFLOGGING
#define MYPRINTF(str,...) printf("c Exttoint " str "\n",  ##__VA_ARGS__)
#else
#define MYPRINTF(str,...) do {} while (0)
#endif

namespace CaDiCaL {
// first hash function for integers
struct IntFirstHash {
public:
  size_t operator() (int el) { return el; }
};

// second hash function for integers, when the first hashing function collides
struct IntSecondHash {
public:
  size_t operator() (int el) { return (321321353 * (size_t) el) | 1; }
};

// default value for the hash-map
struct IntTumb {
public:
  std::pair<int, int> operator() () { return std::pair<int, int> (0, 0); }
};

// Equality
struct IntEqualTo {
public:
  bool operator() (int a, int b) { return a == b; }
};

// This class encapsulates the mapping from external literals to
// internal literals.
//
// We experimented with using a vector or a hashmap. The former is
// faster in the SMT context, but makes it impossible to read a CNF
// with a single literal of size 1000000.
//
// The class uses either a vector or an hash-map if the vector is too
// empty.
//
//
struct ExtToInt {

  // are we using a hash-map or still a vector?
  bool use_hash_map;
  // hash-map mapping external 'idx' to internal 'ilit'
  hashmap<int, int, IntFirstHash, IntSecondHash, IntTumb, IntEqualTo> h_e2i;
  // vector mapping external 'idx' to internal 'ilit'
  array_hashmap vec_e2i;
  int limit_to_check = 1e6; // limit to check when adding literals to switch from vector to hashmap

  // returns the corresponding ilit or the default value.
  Key find_or_default (int key, int default_el) const {
    if (use_hash_map) {
      auto it = h_e2i.find (key);
      if (it.first == IntTumb () ().first)
        return default_el;
      return it.second;
    } else {
      if ((size_t) key >= vec_e2i.table.size ())
        return default_el;
      return vec_e2i[key];
    }
  }

  // check if we need to compress the representation or not
  void maybe_compress (int max_var);

  // returns the corresponding ilit, assuming that there is an ilit.
  int operator[] (int i) {
    if (use_hash_map)
      return h_e2i[i];
    return vec_e2i[i];
  }

  // update the mapping
  void update (int i, int j) {
    if (use_hash_map)
      h_e2i.update(i , j);
    return vec_e2i.update(i, j);
  }

  // insert the elit mapping it to the ilit j.
  void insert (int i, int j) {
    if (use_hash_map)
      h_e2i.insert (i , j);
    if (i > limit_to_check) {
      // ensure that we do not test too often
      // when adding literals one-by-one.
      if (limit_to_check <= std::numeric_limits<int>::max () / 2)
        limit_to_check *= 2;
      else
	limit_to_check = std::numeric_limits<int>::max ();
      if (vec_e2i.table.size ()) {
        maybe_compress (vec_e2i.table.size () - 1);
      } else {
        use_hash_map = true;
        erase_vector (vec_e2i.table);
        return h_e2i.insert (i, j);
      }
    }
    return vec_e2i.insert (i, j);
  }

  // find, mimics the iterator from hash-maps
  std::pair<int, int> find (int i) {
    if (use_hash_map)
      return h_e2i.find (i);
    return vec_e2i.find (i);
  }

  // is the container empty?
  inline bool empty () {
    if (use_hash_map)
      return h_e2i.empty ();
    return vec_e2i.empty ();
  }

private:
  // compress the representation from a vector to the hash-map
  void compress ();
};

} // namespace CaDiCaL

#undef MYPRINTF
#endif