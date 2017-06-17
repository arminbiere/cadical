#ifndef _bins_hpp_INCLUDED
#define _bins_hpp_INCLUDED

// We want to have those 'shrink_bins' and 'erase_bins' below inlined,
// because those call inlined functions themself.  Thus this file here
// really needs the definition of 'util.hpp', where those latter functions
// are defined.  However, since we want to keep the includes in
// 'internal.hpp' alphabetically sorted, we have to include this header file
// here in contrast to our policy not to have additional 'include'
// directives in other header files.

#include "util.hpp"

namespace CaDiCaL {

using namespace std;

typedef vector<int> Bins;

inline void shrink_bins (Bins & bs) { shrink_vector (bs); }
inline void erase_bins (Bins & bs) { erase_vector (bs); }

typedef Bins::iterator bins_iterator;
typedef Bins::const_iterator const_bins_iterator;

};

#endif
