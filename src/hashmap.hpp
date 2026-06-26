#ifndef _hashmap_hpp_INCLUDED
#define _hashmap_hpp_INCLUDED

#include <cassert>
#include <functional>
#include <iostream>
#include <unordered_map>
#include <vector>

// for debugging (we cannot use LOG)
// guard to avoid warnings.
//#define MYPRINTFLOGGING
#ifdef MYPRINTFLOGGING
#define MYPRINTF(str,...) printf("c HASHMAP " str "\n",  ##__VA_ARGS__)
#else
#define MYPRINTF(str,...) do {} while (0)
#endif

namespace CaDiCaL {

template <class Key, class Element,
  class FirstHash,
  class SecondHash,
  class Tumb,
  class KeyEqual = std::equal_to<Key>>
class hashmap {
private:
  using pair = std::pair<Key, Element>;
  pair *table;
  size_t size = 0;
  size_t capacity = 0;
  FirstHash hash1;
  SecondHash hash2;
#ifndef NDEBUG
  std::unordered_map<Key, Element> map;
#endif

  size_t reduce_hash1 (Key k) const {
    return FirstHash () (k) & (capacity - 1);
  }

  size_t reduce_hash2 (Key k) const {
    return SecondHash () (k) & (capacity - 1);
  }
  bool full () const {
    return size >= capacity / 4 * 3;
  }

  void enlarge_intern () {
    assert (full ());
    const size_t old_capacity = capacity;
    capacity = capacity ? 2 * capacity : 4;
    MYPRINTF ("enlarging intern from %zd to %zd\n", old_capacity, capacity);
    pair *old_table = table;
    table = new pair[capacity];

    for (size_t i = 0; i < capacity; ++i)
      table[i] = Tumb () ();

    for (size_t i = 0; i < old_capacity; ++i) {
      const pair& e = old_table[i];
      if (KeyEqual () (e.first, Tumb () ().first))
        continue;
      if (KeyEqual () (e.second, Tumb () ().second))
        continue;
      non_resizing_insert (e.first, e.second);
    }

    delete[] old_table;
  }

  void non_resizing_insert (Key k, Element el) {
    size_t pos = reduce_hash1(k);
    assert (pos < capacity);
    const pair &e = table[pos];
    size_t x = 0;

    if (!KeyEqual () (e.first, Tumb () ().first) && !KeyEqual () (table[pos].first, k)) {
      const size_t delta = reduce_hash2 (k);
      MYPRINTF("hash1: %zd, hash2: %zd", pos, delta);
      assert (delta & 1);
      do {
        pos += delta;
        if (pos >= capacity)
          pos -= capacity;
        assert (pos < capacity);
        ++x;
        assert (x <= capacity);
        MYPRINTF("testing pos %zd", pos);
      } while (!KeyEqual () (table[pos].first, Tumb () ().first) && !KeyEqual () (table[pos].first, k));
    }

    if (KeyEqual () (table[pos].first, k))
      MYPRINTF("inserting %d mapped to %d at position %zd", k, el, pos);
    else
      MYPRINTF("updating %d mapped to %d at position %zd", k, el, pos);
    table[pos] = std::make_pair (k,el);

    for (size_t i = 0; i < capacity; ++i) {
      assert (i == pos || !KeyEqual () (table[i].first, k));
    }

    ++size;
  #ifndef NDEBUG
    map[k] = el;
  #endif
  }

public:
  std::pair<Key,Element> find (Key k) const {
    size_t pos = reduce_hash1(k);
    assert (pos < capacity);
    const pair &e = table[pos];
    MYPRINTF("find %d", k);

    if (KeyEqual () (e.first, Tumb () ().first))
      return Tumb () ();

    if (!KeyEqual () (e.first, k)) {
      const size_t delta = reduce_hash2 (k);
      size_t searched = 1;
      assert (delta & 1);
      do {
        pos += delta;
        if (searched++ == capacity)
          return Tumb () ();
        if (pos >= capacity)
          pos -= capacity;
        assert (pos < capacity);
        if (KeyEqual () (table[pos].first, Tumb () ().first))
          return table[pos];
      } while (!KeyEqual () (table[pos].first, k));
    }

    const pair &f = table[pos];
    assert (KeyEqual () (f.first, k));
  #ifndef NDEBUG
    assert (map.find (k) != map.end () && map.find (k)->second == f.second);
  #endif
    MYPRINTF("find %d -> %d", k, f.second);
    return f;
  }

  std::pair<Key,Element> find (Key k) {
    MYPRINTF("find %d", k);
    size_t pos = reduce_hash1(k);
    assert (pos < capacity);
    pair &e = table[pos];

    if (KeyEqual () (e.first, Tumb () ().first))
      return Tumb () ();

    if (!KeyEqual () (e.first, k)) {
      const size_t delta = reduce_hash2 (k);
      size_t searched = 1;
      assert (delta & 1);
      do {
        pos += delta;
        if (searched++ == capacity)
          return Tumb () ();
        if (pos >= capacity)
          pos -= capacity;
        assert (pos < capacity);
        if (KeyEqual () (table[pos].first, Tumb () ().first)) {
          assert (table[pos].second == Tumb () ().second);
          return table[pos];
        }
      } while (!KeyEqual () (table[pos].first, k));
    }

    pair &f = table[pos];
    assert (KeyEqual () (f.first, k));
  #ifndef NDEBUG
    assert (map[k] == f.second);
  #endif
    MYPRINTF("find %d -> %d", k, f.second);
    return f;
  }

  void insert (Key k, Element el) {
    if (full ())
      enlarge_intern();
    non_resizing_insert (k, el);
  }

  void update (Key k, Element el) {
    assert (find (k) != Tumb ()());
    non_resizing_insert (k, el);
  }
  bool empty () const {
    return !size;
  }

  Element operator[] (Key k) const {
#ifndef NDEBUG
    assert ((map.find (k) == map.end ()) || map.find (k)->second == find (k).second);
#endif
    assert (find (k).second);
    return find (k).second;
  }
  Element operator[] (Key k) {
#ifndef NDEBUG
    assert ((map.find (k) == map.end ()) || map.find (k)->second == find (k).second);
#endif
    assert (find (k).second);
    return find (k).second;
  }

  pair* begin () {
    return table;
  }

  pair* end () {
    return table + capacity;
  }

  hashmap () {
    capacity = 4;
    table = new pair[4];
    for (size_t i = 0; i < capacity; ++i)
      table[i] = Tumb () ();
  }

  ~hashmap () {
    delete [] table;
  }

  void enlarge_intern (size_t new_capacity) {
    assert (full ());
    if (new_capacity < capacity)
      return;
    const size_t old_capacity = capacity;
    while (capacity <= new_capacity)
      capacity *= 2;
    MYPRINTF ("enlarging intern from %zd to %zd\n", old_capacity, capacity);
    pair *old_table = table;
    table = new pair[capacity];

    for (size_t i = 0; i < capacity; ++i)
      table[i] = Tumb () ();

    for (size_t i = 0; i < old_capacity; ++i) {
      const pair& e = old_table[i];
      if (KeyEqual () (e.first, Tumb () ().first))
        continue;
      // don't reallocate deleted elements
      if (KeyEqual () (e.second, Tumb () ().second))
        continue;
      non_resizing_insert (e.first, e.second);
    }

    delete[] old_table;
  }
};



using Key = int;
using Element = int;
class array_hashmap {
public:
  std::vector<Element> table;
  size_t size = 0;
  size_t capacity = 0;

  void non_resizing_insert (Key k, Element el) {
    table[k] = el;
  }

public:
  std::pair<Key,Element> find (Key k) const {
    if ((size_t)k >= table.size ())
      return std::pair<int,int>(0,0);
    return std::pair<int,int>(k, table[k]);
  }

  std::pair<Key,Element> find (Key k) {
    if ((size_t)k >= table.size ())
      return std::pair<int,int>(0,0);
    return std::pair<int,int>(k, table[k]);
  }

  void insert (Key k, Element el) {
    if ((size_t)k >= table.size ())
      table.resize (k+1);
    table[k] = el;
  }

  void update (Key k, Element el) {
    non_resizing_insert (k, el);
  }
  bool empty () const {
    return !size;
  }

  Element operator[] (Key k) const {
    assert ((size_t)k < table.size ());
    return table[k];
  }

  std::vector<int>::iterator begin () {
    return table.begin();
  }

  std::vector<int>::iterator  end () {
    return table.end ();
  }

};


} // namespace CaDiCaL

#undef MYPRINTF
#endif
