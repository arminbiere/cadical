#ifndef _arena_hpp_INCLUDED
#define _arena_hpp_INCLUDED

#include <cassert>
#include <cstdlib>
#include <cstring>

namespace CaDiCaL {

// This memory allocation arena provides fixed size pre-allocated memory for
// the moving garbage collector 'move_non_garbage_clauses' in 'reduce.cpp'
// to hold clauses which should survive garbage collection.

class Internal;

// The standard sequence of using an arena is as follows:
//
//   Arena arena;
//   ...
//   arena.prepare (bytes);
//   ... = arena.copy (bytes1);
//   ... = arena.copy (bytesn);
//   assert (bytes1 + ... + bytesn <= bytes);
//   arena.swap ();
//   ...
//   if (!arena.contains (p)) delete p;
//   ...
//   arena.prepare (bytes);
//   ... = arena.copy (bytes1);
//   ... = arena.copy (bytesn);
//   assert (bytes1 + ... + bytesn <= bytes);
//   arena.swap ();
//   ...
//
// One has to be really careful with references to arena memory.

class Arena {

  Internal * internal;

  struct { char * start, * top, * end; } from, to;

public:

  Arena (Internal *);
  ~Arena ();

  // Does the memory pointed to by 'p' belong to this arena? More precisely
  // to the 'from' space, since that is the only one remaining after 'swap'.
  //
  bool contains (void * p) const {
    char * c = (char *) p;
    return from.start <= c && c < from.top;
  }

  // Prepare 'to' space to hold that amount of memory.  Precondition is that
  // the 'to' space is empty.  The following sequence of 'copy' operations
  // can use as much memory in sum as pre-allocated here.
  //
  void prepare (size_t bytes);

  // Allocate that amount of memory in 'to' space.  This assumes the 'to'
  // space has been prepared to hold enough memory with 'prepare'.  Then
  // copy the memory pointed to by 'p' of size 'bytes'.
  //
  char * copy (const char * p, size_t bytes) {
    char * res = to.top;
    to.top += bytes;
    assert (to.top <= to.end);
    memcpy (res, p, bytes);
    return res;
  }

  // Completely delete 'from' space and then replace 'from' by 'to' (by
  // pointer swapping).  Everything previously allocated (in 'from') and not
  // explicitly copied to 'to' with 'copy' becomes invalid.
  //
  void swap ();
};

};

#endif
