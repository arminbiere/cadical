#ifndef _cector_hpp_INCLUDED
#define _cector_hpp_INCLUDED

#include <climits>
#include <cstdlib>
#include <cassert>
#include <vector>

namespace CaDiCaL {

template<class T> class cector {

  T * _begin;
  unsigned _size;
  unsigned _capacity;

public:

  size_t size () const { return (size_t) _size; }
  size_t capacity () const { return (size_t) _capacity; }

private:

  bool full () const { return size () == capacity (); }

  void enlarge () {
    assert (full ());
    if (!_capacity) _capacity = 1;
    else if (_capacity == UINT_MAX) throw std::bad_alloc ();
    else if (_capacity >= UINT_MAX/2) _capacity = UINT_MAX;
    else _capacity *= 2;
    _begin = (T*) realloc (_begin, _capacity * sizeof (T));
    if (!_begin) throw std::bad_alloc ();
  }

public:

  cector () : _begin (0), _size (0), _capacity (0) { }
  ~cector () { if (_begin) free (_begin); }

  cector & operator = (cector & other) {
    _begin = other._begin;
    _size = other._size;
    _capacity = other._capacity;
    other._begin = 0;
    other._size = 0;
    other._capacity = 0;
    return *this;
  }

  void push_back (const T & w) {
    if (full ()) enlarge ();
    _begin[_size++] = w;
  }

  void resize (size_t i) {
    assert (i <= size ());
    _size = i;
  }

  void shrink () {
    assert (_size <= _capacity);
    if (_size == _capacity) return;
    _capacity = _size;
    _begin = (T*) realloc (_begin, _capacity * sizeof (T));
    if (_capacity && !_begin) throw std::bad_alloc ();
  }

  typedef T * iterator;
  typedef T const * const_iterator;

  iterator begin () { return _begin; }
  iterator end () { return _begin + _size; }

  const_iterator begin () const { return _begin; }
  const_iterator end () const { return _begin + _size; }
};

};

#endif
