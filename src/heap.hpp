#ifndef _heap_hpp_INCLUDED
#define _heap_hpp_INCLUDED

#include "util.hpp"

#include <cassert>
#include <vector>
#include <climits>

namespace CaDiCaL {

using namespace std;

// This is a priority queue with updates for positive integers implemented
// as binary heap.  We need to map integer elements added (through
// 'push_back') to positions on the binary heap in 'array'. This map is
// stored in the 'pos' array.  As a consequence only positive elements
// can be added.  This approach is also really wasteful (at least in terms
// of memory) if only few and a sparse set of integers is added.  So it
// should not be used in this situation.  A generic priority queue would
// implement that mapping externally provided by another template parameter.

template<class C> class pos_int_heap {

  vector<int> array;	// actual binary heap
  vector<int> pos;	// positions of 'int' elements in heap
  C less;		// less-than for 'int' elements

  // Map an 'int' element to its position entry in the 'pos' map.
  //
  int & index (int e) {
    assert (e >= 0);
    while ((size_t) e >= pos.size ()) pos.push_back (-1);
    int & res = pos[e];
    assert (res < 0 || (size_t) res < array.size ());
    return res;
  }

  bool has_parent (int e) { return index (e) > 0; }
  bool has_left (int e)   { return (size_t) 2*index (e) + 1 < size (); }
  bool has_right (int e)  { return (size_t) 2*index (e) + 2 < size (); }

  int parent (int e) { assert (has_parent (e)); return array[ (index (e) - 1)/2]; }
  int left   (int e) { assert (has_left (e));   return array[2*index (e) + 1]; }
  int right  (int e) { assert (has_right (e));  return array[2*index (e) + 2]; }

  // Exchange 'int' elements 'a' and 'b' in 'array' and fix their positions.
  //
  void exchange (int a, int b) {
    int & i = index (a), & j = index (b);
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
#if 1
    for (size_t i = 0; i < array.size (); i++) {
      size_t l = 2*i + 1, r = 2*i + 2;
      if (l < array.size ()) assert (!less (array[i], array[l]));
      if (r < array.size ()) assert (!less (array[i], array[r]));
      assert ((size_t) array[i] < pos.size ());
      assert (i == (size_t) pos[array[i]]);
    }
    for (size_t i = 0; i < pos.size (); i++) {
      assert (i <= (size_t) INT_MAX);
      if (pos[i] < 0) continue;
      assert ((size_t) pos[i] < array.size ());
      assert (array[pos[i]] == (int) i);
    }
#endif
  }

public:

  pos_int_heap (const C & c) : less (c) { }

  // Number of elements in the heap.
  //
  size_t size () const { return array.size (); }

  // Check if no more elements are in the heap.
  //
  bool empty () const { return array.empty (); }

  // Check whether 'e' is already int the heap.
  //
  bool contains (int e) { 
    assert (0 <= e);
    if ((size_t) e >= pos.size ()) return false;
    return pos[e] >= 0;
  }

  // Add a new (not contained) element 'e' to the heap.
  //
  void push_back (int e) {
    assert (0 <= e);
    assert (!contains (e));
    assert (array.size () <= (size_t) INT_MAX);
    int i = (int) array.size ();
    if (i == INT_MAX) throw bad_alloc ();
    array.push_back (e);
    index (e) = i;
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
    int res = array[0], last = -1;
    if (size () > 1) exchange (res, (last = array.back ()));
    index (res) = -1;
    array.pop_back ();
    if (last >= 0) down (last);
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
    for (size_t i = 0; i < pos.size (); i++) pos[i] = -1;
  }

  void erase () { erase_vector (array); erase_vector (pos); }

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
