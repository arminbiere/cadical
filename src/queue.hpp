#ifndef _queue_hpp_INCLUDED
#define _queue_hpp_INCLUDED

namespace CaDiCaL {

// VMTF decision queue ordered by 'bumped'.

struct Queue {

  int first, last;    // anchors (head/tail) for doubly linked list
  int unassigned;     // all variables after this one are assigned
  long bumped;        // bumped stamp of 'bassigned'

  Queue () : first (0), last (0), unassigned (0), bumped (0) { }

  void dequeue (Link * ltab, Link * l) {
    if (l->prev) ltab[l->prev].next = l->next; else first = l->next;
    if (l->next) ltab[l->next].prev = l->prev; else last = l->prev;
  }

  void enqueue (Link * ltab, Link * l) {
    if ((l->prev = last)) ltab[last].next = l - ltab; else first = l - ltab;
    last = l - ltab;
    l->next = 0;
  }

  void init (Internal *, int new_max_var);
};

};

#endif
