#ifndef _link_hpp_INCLUDED
#define _link_hpp_INCLUDED

namespace CaDiCaL {

struct Var;

// Links for double linked decision VMTF queue.

struct Link {

  Link * prev, * next;

  Link () : prev (0), next (0) { }
};

};

#endif
