#ifndef _flags_hpp_INCLUDED
#define _flags_hpp_INCLUDED

namespace CaDiCaL {

struct Flags {         // Variable flags.


  bool seen      : 1;  // seen in generating first UIP clause in 'analyze'
  bool poison    : 1;  // can not be removed in 'minimize/shrink'
  bool removable : 1;  // can be removed in 'minimize/shrink'
  bool clause    : 1;  // part of learned clause in 'minimize/shrink'
  bool added     : 1;  // added since last 'subsume' round
  bool removed   : 1;  // removed since last 'elim' round

  Flags () :
    seen (false),
    poison (false),
    removable (false),
    clause (false),
    added (true),
    removed (true)
  { }
};

};

#endif
