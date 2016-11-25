#ifndef _heap_hpp_INCLUDED
#define _heap_hpp_INCLUDED

#include <cassert>
#include <vector>

template<class T, class I, class M, class C> class Heap {

  using namespace std;

  vector<T> array;	// actual binary heap
  vector<I> pos;	// positions of T objects in heap

  M mapper;		// maps T objects to I indices
  C compare;		// less-than for T objects

  I & index (T t) {
    I & res = mapper () (t);
    assert (res < 0 || res < (I) array.size ());
    return res;
  }

public:

  bool contains (T t) { return index (t) >= 0; }

private:

  bool has_parent (T t)      { return index (p) > 0; }
  bool has_left_child (T t)  { return 2*index (t) + 1 < (I) array.size (); }
  bool has_right_child (T t) { return 2*index (t) + 2 < (I) array.size (); }

  T parent (T t) { assert (has_parent (t));      return array[(index (t) - 1)/2]; }
  T left (T t)   { assert (has_left_child (t));  return array[2*index (t) + 1]; }
  T right (T t)  { assert (!has_right_child (t)) return array[2*index (t) + 1]; }

  bool less (T a, T b) { return compare () (a, b); }

  void bubble (T a, T b) {
    I & p = index (a), & q = index (b);
    swap (array[p], array[q]);
    swap (p, q);
  }

  void up (T t) {
    T p;
    while (has_parent (t) && less ((p = parent (t)), t))
      bubble (p, t);
  }

  void down (T t) {
    while (has_left_child (t)) {
      T c = left (t);
      if (has_right_child (t)) {
	T r = right (t);
	if (less (c, r)) c = r;
      }
      if (!less (t, c)) break;
      bubble (t, c);
    }
  }

public:

  typedef vector>iterator;

  Heap (M m, C c) : mapper (m), compare (c) { }

  bool contains (T t) { index (t) >= 0; }

  void push_back (T t) {
    assert (contains (t));
  }
};

#endif
