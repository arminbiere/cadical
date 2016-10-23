#ifndef _flags_hpp_INCLUDED
#define _flags_hpp_INCLUDED

// Variable flags related to 'analyze' and 'minimize'.

namespace CaDiCaL {

enum Flag {
  SEEN = 1,      // seen in generating first UIP clause in 'analyze'.
  POISON = 2,    // can not be removed in 'minimize'.
  REMOVABLE = 4  // can be removed in 'minimize'.
};


class Flags {

  unsigned char byte;  // one byte bit mask of Flags above

public:

  Flags () : byte (0) { }

  bool seen () const { return (byte & SEEN) != 0; }
  bool poison () const { return (byte & POISON) != 0; }
  bool removable () const { return (byte & REMOVABLE) != 0; }

  // Set flag, e.g., 'set (SEEN)', 'set (POISON)', or 'set (REMOVABLE)'.
  //
  inline void set (Flag f) {
    assert (!(byte & f));
    assert (f == SEEN || f == POISON || f == REMOVABLE);
    byte |= f;
  }

  // Any flag set?
  //
  operator bool () const { return byte != 0; }

  void reset () { byte = 0; }
};

};

#endif
