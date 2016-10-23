#ifndef _flags_hpp_INCLUDED
#define _flags_hpp_INCLUDED

// Variable flags related to 'analyze' and 'minimize'.

namespace CaDiCaL {

enum Flag {
  SEEN      = 1, // seen in generating first UIP clause in 'analyze'.
  POISON    = 2, // can not be removed in 'minimize'.
  REMOVABLE = 4  // can be removed in 'minimize'.

  // Powers of two since these constants are used in a bit-set in 'Flags'.
};

class Flags {

  // One byte bit-set of flags above.  Note that we want a fast check that
  // no bit is set (the 'operator bool ()' function below) and thus do not
  // want to use bit-fields nor 'bool' members, which would be needed to be
  // checked in turn otherwise.  We hide read operators of those bits behind
  // the 'seen ()' etc. functions but for simpler naming only have one 'set'
  // functions for all flags.  It further turns out that 'g++' and 'clang++'
  // actually figure out that 'sizeof (Flags) == 1', so 'Flags' needs
  // exactly one byte and more important that 'new Flags[10]' is allocated
  // as a byte array (and needs 10 bytes).
  //
  // Used bit-sets:
  //                       0   no flag set
  //   SEEN             == 1   seen in 'minimize' but not minimized yet
  //   SEEN | POISON    == 3   seen in 'minimize' and can not be removed
  //   SEEN | REMOVABLE == 5   seen in 'minimize' and can be removed
  //   POISON           == 4   can not be removed in 'minimize'
  //
  // Using the 'operator bool ()' function in 'analyze' seems to be a hot
  // spot within 'analyze'.  This is the main reason for keeping 'Flags'
  // seperate.  Originally we used 'bool seen' etc. members in 'Var.'
  //
  unsigned char byte;

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
