#ifndef _elim_hpp_INCLUDED
#define _elim_hpp_INCLUDED

#include "heap.hpp"

namespace CaDiCaL {

class Internal;

struct more_noccs2 {
  Internal * internal;
  more_noccs2 (Internal * i) : internal (i) { }
  bool operator () (int a, int b);
};

typedef heap<more_noccs2> ElimSchedule;

};

#endif
