#ifndef _elim_hpp_INCLUDED
#define _elim_hpp_INCLUDED

#include "heap.hpp"     // Alphabetically after 'elim.hpp'.

namespace CaDiCaL {

struct Internal;

struct elim_more {
  Internal * internal;
  elim_more (Internal * i) : internal (i) { }
  bool operator () (unsigned a, unsigned b);
};

typedef heap<elim_more> ElimSchedule;

struct Eliminator {

  Internal * internal;
  ElimSchedule schedule;

  Eliminator (Internal * i) : internal (i), schedule (elim_more (i)) { }
  ~Eliminator ();

  queue<Clause*> backward;

  Clause * dequeue ();
  void enqueue (Clause *);

  vector<Clause *> gates;
  vector<int> marked;
};

}

#endif
