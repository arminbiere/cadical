#ifndef _queue_hpp_INCLUDED
#define _queue_hpp_INCLUDED

namespace CaDiCaL {

class Internal;

// VMTF decision queue ordered by 'Link.bumped'.

struct Queue {

  int first, last;    // anchors (head/tail) for doubly linked list
  int bassigned;      // all variables after this one are assigned
  long bumped;        // bumped stamp of 'bassigned'

  Queue () : first (0), last (0), bassigned (0), bumped (0) { }

  void dequeue (Link * ltab, Link * l) {
    if (l->prev) ltab[l->prev].next = l->next; else first = l->next;
    if (l->next) ltab[l->next].prev = l->prev; else last = l->prev;
  }

  void enqueue (Link * ltab, Link * l) {
    if ((l->prev = last)) ltab[last].next = l - ltab; else first = l - ltab;
    last = l - ltab;
    l->next = 0;
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
