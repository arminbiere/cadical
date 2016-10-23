#ifndef _queue_hpp_INCLUDED
#define _queue_hpp_INCLUDED

#include "var.hpp"

namespace CaDiCaL {

class Internal;

// VMTF decision queue ordered by 'Var.bumped'.

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

  // Initialize VMTF queue from current 'max_var+1' to 'new_max_var'.  This
  // incoporates an initial variable order.  We currently simply assume
  // that variables with smaller index are more important.
  //
  void init (Internal *, int new_max_var);

  // Save and restore the variable order for resizing the solver.
  //
  void save (Internal *, vector<int> &);
  void restore (Internal *, const vector<int> &);
};

};

#endif
