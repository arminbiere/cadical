#ifndef _queue_hpp_INCLUDED
#define _queue_hpp_INCLUDED

namespace CaDiCaL {

class Solver;

// VMTF decision queue

struct Queue {

  Var * first, * last;  // anchors (head/tail) for doubly linked list
  Var * assigned;       // all variables after this one are assigned

  Queue () : first (0), last (0), assigned (0) { }

  void dequeue (Var * v) {
    if (v->prev) v->prev->next = v->next; else first = v->next;
    if (v->next) v->next->prev = v->prev; else last = v->prev;
  }

  void enqueue (Var * v) {
    if ((v->prev = last)) last->next = v; else first = v;
    last = v;
    v->next = 0;
  }

  void init (Solver *);
};

};

#endif
