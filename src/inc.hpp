#ifndef _inc_hpp_INCLUDED
#define _inc_hpp_INCLUDED

namespace CaDiCaL {

struct Inc {
  long reduce;   // reduce interval increment
  long redinc;   // reduce increment increment
  long subsume;  // subsumption interval increment

  Inc () : reduce (0), redinc (0), subsume (0) { }
};

};

#endif
