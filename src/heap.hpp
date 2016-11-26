#ifndef _heap_hpp_INCLUDED
#define _heap_hpp_INCLUDED

#include <cassert>
#include <vector>

using namespace std;

template<class C> class int_heap {

  vector<int> array;	// actual binary heap
  vector<int> pos;	// positions of int objects in heap

  C less;		// less-than for int objects

  int & index (int t) {
    assert (t > 0);
    while (t >= (int) pos.size ()) pos.push_back (-1);
    int & res = pos[t];
    assert (res < 0 || res < (int) array.size ());
    return res;
  }

public:

  bool contains (int t) { 
    if (t >= (int) pos.size ()) return false;
    return pos[t] >= 0;
  }

private:

  bool has_parent (int t)      { return index (t) > 0; }
  bool has_left_child (int t)  { return 2*index (t) + 1 < (int) array.size (); }
  bool has_right_child (int t) { return 2*index (t) + 2 < (int) array.size (); }

  int parent (int t) { assert (has_parent (t));      return array[(index (t) - 1)/2]; }
  int left (int t)   { assert (has_left_child (t));  return array[2*index (t) + 1]; }
  int right (int t)  { assert (has_right_child (t)); return array[2*index (t) + 1]; }

  void bubble (int a, int b) {
    int & p = index (a), & q = index (b);
    swap (array[p], array[q]);
    swap (p, q);
  }

  void up (int t) {
    int p;
    while (has_parent (t) && less ((p = parent (t)), t))
      bubble (p, t);
  }

  void down (int t) {
    while (has_left_child (t)) {
      int c = left (t);
      if (has_right_child (t)) {
	int r = right (t);
	if (less (c, r)) c = r;
      }
      if (!less (t, c)) break;
      bubble (t, c);
    }
  }

public:

  int_heap (const C & c) : less (c) { }

  void push_back (int t) {
    assert (0 < t);
    assert (!contains (t));
    int i = (int) array.size ();
    array.push_back (t);
    index (t) = i;
    up (t);
    down (t);
  }

  typedef typename vector<int>::iterator iterator;
  typedef typename vector<int>::const_iterator const_iterator;

  iterator begin () { return array.begin (); }
  iterator end () { return array.end (); }

  const_iterator begin () const { return array.begin (); }
  const_iterator end () const { return array.end (); }
};

#endif
