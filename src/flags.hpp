#ifndef _flags_hpp_INCLUDED
#define _flags_hpp_INCLUDED

namespace CaDiCaL {

struct Flags {        // Variable flags.

  //  The first set of flags is related to 'analyze' and 'minimize'.
  //
  bool seen      : 1; // seen in generating first UIP clause in 'analyze'
  bool keep      : 1; // keep in learned clause in 'minimize'
  bool poison    : 1;    // can not be removed in 'minimize'
  bool removable : 1;    // can be removed in 'minimize'
  bool shrinkable : 1; // can be removed in 'shrink'

  // These three variable flags are used to schedule clauses in subsumption
  // ('subsume'), variables in bounded variable elimination ('elim') and in
  // hyper ternary resolution ('ternary').
  //
  bool elim      : 1; // removed since last 'elim' round (*)
  bool subsume   : 1; // added since last 'subsume' round (*)
  bool ternary   : 1; // added in ternary clause since last 'ternary' (*)

  // These literal flags are used by blocked clause elimination ('block').
  //
  unsigned char block : 2;   // removed since last 'block' round (*)
  unsigned char skip : 2;    // skip this literal as blocking literal

  // Bits for handling assumptions.
  //
  unsigned char assumed : 2;
  unsigned char failed : 2;

  enum {
    UNUSED      = 0,
    ACTIVE      = 1,
    FIXED       = 2,
    ELIMINATED  = 3,
    SUBSTITUTED = 4,
    PURE        = 5
  };

  unsigned char status : 3;

  // Initialized explicitly in 'Internal::init' through this function.
  //
  Flags () {
    seen = keep = poison = removable = shrinkable = false;
    subsume = elim = ternary = true;
    block = 3u;
    skip = assumed = failed = 0;
    status = UNUSED;
  }

  bool unused () const { return status == UNUSED; }
  bool active () const { return status == ACTIVE; }
  bool fixed () const { return status == FIXED; }
  bool eliminated () const { return status == ELIMINATED; }
  bool substituted () const { return status == SUBSTITUTED; }
  bool pure () const { return status == PURE; }

  // The flags marked with '(*)' are copied during 'External::copy_flags',
  // which in essence means they are reset in the copy if they were clear.
  // This avoids the effort of fruitless preprocessing the copy.

  void copy (Flags & dst) const {
    dst.elim = elim;
    dst.subsume = subsume;
    dst.ternary = ternary;
    dst.block = block;
  }
};

}

#endif
