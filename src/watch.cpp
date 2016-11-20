#include "internal.hpp"
#include "iterator.hpp"
#include "macros.hpp"

namespace CaDiCaL {

void Internal::init_watches () {
  assert (!wtab);
  wtab = new Watches [2*vsize];
}

void Internal::reset_watches () {
  assert (wtab);
  delete [] wtab;
  wtab = 0;
}

void Internal::connect_watches () {
  START (connect);
  assert (watches ());
  LOG ("connecting all watches");
  const const_clause_iterator end = clauses.end ();
  for (const_clause_iterator i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (!c->garbage) watch_clause (c);
  }
  STOP (connect);
}

#ifdef WATCHES

void Watches::enlarge () {
  assert (full ());
  if (_begin) {
    size_t bytes = (1u << _log_capacity++) * sizeof (Watch);
    char * p = new char[2*bytes];
    memcpy (p, _begin, bytes);
    delete [] (char*) _begin;
    _begin = (Watch *) p;
  } else {
    _begin = (Watch*) new char[sizeof (Watch)];
    assert (!_log_capacity);
  }
}

void Watches::shrink () {
  if (!_begin) return;
  if (_size) {
    unsigned new_log_capacity = _log_capacity;
    while (new_log_capacity && _size <= (1ull << (new_log_capacity - 1)))
      new_log_capacity--;
    if (new_log_capacity == _log_capacity) return;
    _log_capacity = new_log_capacity;
    size_t bytes = (1ull << _log_capacity) * sizeof (Watch);
    char * p = new char[bytes];
    memcpy (p, _begin, bytes);
    delete [] (char*) _begin;
    _begin = (Watch *) p;
  } else {
    delete [] _begin; 
    _log_capacity = 0;
    _begin = 0;
  }
}

#endif

};
