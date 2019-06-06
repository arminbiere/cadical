#ifndef _bins_hpp_INCLUDED
#define _bins_hpp_INCLUDED

#include "util.hpp"     // Alphabetically after 'bins'.

namespace CaDiCaL {

using namespace std;

typedef vector<int> Bins;

inline void shrink_bins (Bins & bs) { shrink_vector (bs); }
inline void erase_bins (Bins & bs) { erase_vector (bs); }

}

#endif
