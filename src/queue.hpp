#ifndef _queue_hpp_INCLUDED
#define _queue_hpp_INCLUDED

namespace CaDiCaL {

// Links for double linked decision queue.

struct Link {

  int prev, next;    // variable indices

  // initialized explicitly in 'init_queue'
};

// Variable move to front (VMTF) decision queue ordered by 'bumped'.  See
// our SAT'15 paper for an explanation on how this works.

struct Queue {

  // We use integers instead of variable pointers.  This is more compact and
  // also avoids issues due to moving the variable table during 'resize'.

  int first, last;    // anchors (head/tail) for doubly linked list
  int unassigned;     // all variables after this one are assigned
  long bumped;        // see 'Internal.update_queue_unassigned'

  Queue () : first (0), last (0), unassigned (0), bumped (0) { }

  // We explicitly provide the mapping of integer indices to links to the
  // following two (inlined) functions.  This avoids including
  // 'internal.hpp' and breaks a cyclic dependency, so we can keep their
  // code here in this header file.  Otherwise they are just ordinary doubly
  // linked list 'dequeue' and 'enqueue' operations.

  inline void dequeue (Link * ltab, Link * l) {
    if (l->prev) ltab[l->prev].next = l->next; else first = l->next;
    if (l->next) ltab[l->next].prev = l->prev; else last = l->prev;
  }

  inline void enqueue (Link * ltab, Link * l) {
    if ((l->prev = last)) ltab[last].next = l - ltab; else first = l - ltab;
    last = l - ltab;
    l->next = 0;
  }
};

};

#endif
