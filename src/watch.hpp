#ifndef _watch_hpp_INCLUDED
#define _watch_hpp_INCLUDED

#ifndef NDEBUG
#include "clause.hpp"
#endif

namespace CaDiCaL {

class Clause;

struct Watch {
  int blit;             // if blocking literal is true do not visit clause
  int size;             // same as 'clause->size'
  Clause * clause;
  Watch (int b, Clause * c, int s) : blit (b), size (s), clause (c) {
    assert (b), assert (c), assert (c->size == s);
  }
  Watch () { }
};

#if 0

typedef vector<Watch> Watches;          // of one literal

inline void shrink_watches (Watches & ws) { shrink_vector (ws); }

typedef vector<Watch>::iterator watch_iterator;
typedef vector<Watch>::const_iterator const_watch_iterator;

#elif 0

#define WATCHES

typedef Watch * watch_iterator;
typedef Watch const * const_watch_iterator;

class Watches {

  Watch * _begin;
  unsigned long _size : 56;
  unsigned _log_capacity : 8;

public:

  size_t size () const { return (size_t) _size; }

  size_t capacity () const {
    return _begin ? (1ull << _log_capacity) : 0ull;
  }

private:

  bool full () const { return size () == capacity (); }
  void enlarge ();

public:

  Watches () : _begin (0), _size (0), _log_capacity (0) { }
  ~Watches () { if (_begin) delete [] _begin; }

  Watches & operator = (Watches & other) {
    _begin = other._begin;
    _size = other._size;
    _log_capacity = other._log_capacity;
    other._begin = 0;
    other._size = 0;
    other._log_capacity = 0;
    return *this;
  }

  void push_back (const Watch & w) {
    if (full ()) enlarge ();
    _begin[_size++] = w;
  }

  void resize (size_t i) {
    assert (i <= size ());
    _size = i;
  }

  void shrink ();

  watch_iterator begin () { return _begin; }
  watch_iterator end () { return _begin + _size; }

  const_watch_iterator begin () const { return _begin; }
  const_watch_iterator end () const { return _begin + _size; }
};

inline void shrink_watches (Watches & ws) { ws.shrink (); }

#else

#define WATCHES

typedef Watch * watch_iterator;
typedef Watch const * const_watch_iterator;

class Watches {

  Watch * _begin;
  unsigned _size;
  unsigned _capacity;

public:

  size_t size () const { return (size_t) _size; }
  size_t capacity () const { return (size_t) _capacity; }

private:

  bool full () const { return size () == capacity (); }
  void enlarge ();

public:

  Watches () : _begin (0), _size (0), _log_capacity (0) { }
  ~Watches () { if (_begin) delete [] _begin; }

  Watches & operator = (Watches & other) {
    _begin = other._begin;
    _size = other._size;
    _log_capacity = other._log_capacity;
    other._begin = 0;
    other._size = 0;
    other._log_capacity = 0;
    return *this;
  }

  void push_back (const Watch & w) {
    if (full ()) enlarge ();
    _begin[_size++] = w;
  }

  void resize (size_t i) {
    assert (i <= size ());
    _size = i;
  }

  void shrink ();

  watch_iterator begin () { return _begin; }
  watch_iterator end () { return _begin + _size; }

  const_watch_iterator begin () const { return _begin; }
  const_watch_iterator end () const { return _begin + _size; }
};

inline void shrink_watches (Watches & ws) { ws.shrink (); }

#endif

};

#endif
