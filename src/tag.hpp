#ifndef _tag_hpp_INCLUDED
#define _tag_hpp_INCLUDED

class Tag {
  unsigned char byte;
public:
  enum { SEEN = 1, POISON = 2, REMOVABLE = 4 };
  Tag () : byte (0) { }
  bool seen () const { return (byte & SEEN) != 0; }
  bool poison () const { return (byte & POISON) != 0; }
  bool removable () const { return (byte & REMOVABLE) != 0; }
  void mark (unsigned t) { byte |= t; }
  operator bool () const { return byte != 0; }
  void reset () { byte = 0; }
};

#endif
