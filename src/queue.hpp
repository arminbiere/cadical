#ifndef _queue_hpp_INCLUDED
#define _queue_hpp_INCLUDED

namespace CaDiCaL {

// VMTF decision queue

struct Queue {

  int first, last;    // anchors (head/tail) for doubly linked list
  int assigned;       // all variables after this one are assigned

  Queue () : first (0), last (0), assigned (0) { }
};

};

#endif
