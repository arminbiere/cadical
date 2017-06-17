#ifndef _elim_hpp_INCLUDED
#define _elim_hpp_INCLUDED

// Since 'ElimSchedule' needs the declaration of the 'heap' container, we
// have to include it here.  This is an exception to the policy of not
// including any header files in other header files than 'internal.hpp'.  In
// principle another possible fix would be to place the include directive
// for this file 'elim.hpp' after 'heap.hpp' but that is violating the other
// policy we have, which tries to keep the include directives in
// 'internal.hpp' alphabetically sorted.

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
