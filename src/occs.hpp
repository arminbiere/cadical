#ifndef _occs_h_INCLUDED
#define _occs_h_INCLUDED

#include <vector>
#include "cector.hpp"

namespace CaDiCaL {

class Clause;
using namespace std;

#if 0
typedef vector<Clause*> Occs;
inline void shrink_occs (Occs & os) { shrink_vector (os); }
inline void erase_occs (Occs & os) { erase_vector (os); }
#else
typedef cector<Clause*> Occs;
inline void shrink_occs (Occs & os) { os.shrink (); }
inline void erase_occs (Occs & os) { os.resize (0); os.shrink (); }
#endif

typedef Occs::iterator occs_iterator;
typedef Occs::const_iterator const_occs_iterator;

};

#endif
