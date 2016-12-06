#ifndef _heap_hpp_INCLUDED
#define _heap_hpp_INCLUDED

#include "util.hpp"

#include <cassert>
#include <vector>
#include <climits>
#include <algorithm>

namespace CaDiCaL {

using namespace std;

// This is a priority queue with updates for integers implemented
// as binary heap.  We need to map integer elements added (through
// 'push_back') to positions on the binary heap in 'array'. This map is
// stored in the 'pos' array for positive and in the 'neg' array for
// negative integers. This approach is really wasteful (at least in terms
// of memory) if only few and a sparse set of integers is added.  So it
// should not be used in this situation.  A generic priority queue would
// implement the mapping externally provided by another template parameter.
// Since we use 'UINT_MAX' as 'not contained' flag, we can only have
// 'UINT_MAX - 1' elements in the heap.

#ifdef BCE
// We currently only need the negative integer schedules for BCE and thus
// adding negative number to the heap is disabled if BCE is not included.
#endif

const unsigned invalid_heap_position = UINT_MAX;

template<class C> class heap {

  vector<int> array;    // actual binary heap
  vector<unsigned> pos; // positions of positive 'int' elements in array
#ifdef BCE
  vector<unsigned> neg; // positions of negative 'int' elements in array
#endif
  C less;               // less-than for 'int' elements

  // Map a positive 'int' element to its position entry in the 'pos' map.
  //
  unsigned & pindex (int e) {
    assert (e >= 0);
    while ((size_t) e >= pos.size ()) pos.push_back (invalid_heap_position);
    unsigned & res = pos[e];
    assert (res == invalid_heap_position || (size_t) res < array.size ());
    return res;
  }

#ifdef BCE
  // Map a negative 'int' element to its position entry in the 'neg' map.
  //
  unsigned & nindex (int e) {
    assert (e < 0);
    size_t n = - (long) e; // beware of 'INT_MIN'
    while (n >= neg.size ()) neg.push_back (-1);
    unsigned & res = neg[n];
    assert (res == invalid_heap_position || (size_t) res < array.size ());
    return res;
  }
#endif

  // Map an 'int' element to its position entry in the 'pos' or 'neg' map.
  //
  unsigned & index (int e) {
#ifdef BCE
    return e >= 0 ? pindex (e) : nindex (e);
#else
    assert (e >= 0);
    return pindex (e);
#endif
  }

  bool has_parent (int e) { return index (e) > 0; }
  bool has_left (int e)   { return (size_t) 2*index (e) + 1 < size (); }
  bool has_right (int e)  { return (size_t) 2*index (e) + 2 < size (); }

  int parent (int e) { assert(has_parent (e));return array[(index(e)-1)/2]; }
  int left   (int e) { assert(has_left (e));  return array[2*index(e)+1]; }
  int right  (int e) { assert(has_right (e)); return array[2*index(e)+2]; }

  // Exchange 'int' elements 'a' and 'b' in 'array' and fix their positions.
  //
  void exchange (int a, int b) {
    unsigned & i = index (a), & j = index (b);
    swap (array[i], array[j]);
    swap (i, j);
  }

  // Bubble up an element as far as necessary.
  //
  void up (int e) {
    int p;
    while (has_parent (e) && less ((p = parent (e)), e))
      exchange (p, e);
  }

  // Bubble down an element as far as necessary.
  //
  void down (int e) {
    while (has_left (e)) {
      int c = left (e);
      if (has_right (e)) {
        int r = right (e);
        if (less (c, r)) c = r;
      }
      if (!less (e, c)) break;
      exchange (e, c);
    }
  }

  // Very expensive checker for the main 'heap' invariant.  Can be enabled
  // to find violations of antisymmetry in the client implementation of
  // 'less', as well of course, bugs in this heap implementation.
  //
  void check () {
#if 0
    assert (array.size () <= invalid_heap_position);
    for (size_t i = 0; i < array.size (); i++) {
      size_t l = 2*i + 1, r = 2*i + 2;
      if (l < array.size ()) assert (!less (array[i], array[l]));
      if (r < array.size ()) assert (!less (array[i], array[r]));
#ifdef BCE
      if (array[i] >= 0) 
#else
      assert (array[i] >= 0);
#endif
      {
        assert ((size_t) array[i] < pos.size ());
        assert (i == (size_t) pos[array[i]]);
      } 
#ifdef BCE
      if (array[i] < 0) {
        assert ((size_t) - (long) array[i] < neg.size ());
        assert (i == (size_t) neg[(size_t) - (long) array[i]]);
      }
#endif
    }
    for (size_t i = 0; i < pos.size (); i++) {
      if (pos[i] == invalid_heap_position) continue;
      assert (pos[i] < array.size ());
      assert (array[pos[i]] == (int) i);
    }
#ifdef BCE
    for (size_t i = 0; i < neg.size (); i++) {
      if (neg[i] == invalid_heap_position) continue;
      assert (neg[i] < array.size ());
      assert (array[neg[i]] == (int) - (long) i);
    }
#endif
#endif
  }

  bool pcontains (int e) const {
    assert (e >= 0);
    if ((size_t) e >= pos.size ()) return false;
    return pos[e] != invalid_heap_position;
  }

#ifdef BCE
  bool ncontains (int e) const {
    assert (e < 0);
    long n = - (long) e; // beware of -INT_MIN overflow
    if (n >= (long) neg.size ()) return false;
    return neg[n] != invalid_heap_position;
  }
#endif

public:

  heap (const C & c) : less (c) { }

  // Number of elements in the heap.
  //
  size_t size () const { return array.size (); }

  // Check if no more elements are in the heap.
  //
  bool empty () const { return array.empty (); }

  // Check whether 'e' is already in the heap.
  //
  bool contains (int e) const {
#ifdef BCE
    return (e < 0) ? ncontains (e) : pcontains (e);
#else
    assert (e >= 0);
    return pcontains (e);
#endif
  }

  // Add a new (not contained) element 'e' to the heap.
  //
  void push_back (int e) {
    assert (!contains (e));
    size_t i = array.size ();
    assert (i < (size_t) invalid_heap_position);
    array.push_back (e);
    index (e) = (unsigned) i;
    up (e);
    down (e);
    check ();
  }

  // Returns the maximum element in the heap.
  //
  int front () const { assert (!empty ()); return array[0]; }

  // Removes the maximum element in the heap.
  //
  int pop_front () {
    assert (!empty ());
    int res = array[0], last = array.back ();
    if (size () > 1) exchange (res, last);
    index (res) = invalid_heap_position;
    array.pop_back ();
    if (size () > 1) down (last);
    check ();
    return res;
  }

  // Notify the heap, that evaluation of 'less' has changed for 'e'.
  //
  void update (int e) {
    assert (contains (e));
    up (e);
    down (e);
    check ();
  }

  void clear () {
    array.clear ();
    pos.clear ();
#ifdef BCE
    neg.clear ();
#endif
  }

  void erase () {
    erase_vector (array);
    erase_vector (pos);
#ifdef BCE
    erase_vector (neg);
#endif
  }

  void shrink () {
    shrink_vector (array);
    shrink_vector (pos);
#ifdef BCE
    shrink_vector (neg);
#endif
  }

  // Standard iterators 'inherited' from 'vector'.
  //
  typedef typename vector<int>::iterator iterator;
  typedef typename vector<int>::const_iterator const_iterator;
  iterator begin () { return array.begin (); }
  iterator end () { return array.end (); }
  const_iterator begin () const { return array.begin (); }
  const_iterator end () const { return array.end (); }
};

};

#endif
