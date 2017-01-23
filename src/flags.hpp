#ifndef _flags_hpp_INCLUDED
#define _flags_hpp_INCLUDED

namespace CaDiCaL {

struct Flags {        // Variable flags.

  bool seen      : 1; // seen in generating first UIP clause in 'analyze'
  bool keep      : 1; // keep in learned clause in 'minimize/shrink'
  bool poison    : 1; // can not be removed in 'minimize/shrink'
  bool removable : 1; // can be removed in 'minimize/shrink'
  bool added     : 1; // added since last 'subsume' round
  bool removed   : 1; // removed since last 'elim' round

  enum {
    ACTIVE      = 0,
    FIXED       = 1,
    ELIMINATED  = 2,
    SUBSTITUTED = 3,
  };

  unsigned char status : 2;

  // initialized explicitly in 'Internal::init' through this

  void init () {
    assert (sizeof (Flags) == 1);
    seen = keep = poison = removable = false;
    added = removed = true;
    status = ACTIVE;
  }

  bool active () const { return status == ACTIVE; }
  bool fixed () const { return status == FIXED; }
  bool eliminated () const { return status == ELIMINATED; }
  bool substituted () const { return status == SUBSTITUTED; }
};

};

#endif
