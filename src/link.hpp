#ifndef _link_hpp_INCLUDED
#define _link_hpp_INCLUDED

namespace CaDiCaL {

// Links for double linked decision queue.

struct Link {

  int prev, next;    // variable indices

  Link () : prev (0), next (0) { }
};

};

#endif
