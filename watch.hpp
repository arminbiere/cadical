#ifndef _watch_hpp_INCLUDED
#define _watch_hpp_INCLUDED

namespace CaDiCaL {

struct Watch {
  int blit;             // if blocking literal is true do not visit clause
  Clause * clause;
  Watch (int b, Clause * c) : blit (b), clause (c) { }
  Watch () { }
};

typedef vector<Watch> Watches;          // of one literal

};

#endif
