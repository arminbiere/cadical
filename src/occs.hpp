#ifndef _occs_h_INCLUDED
#define _occs_h_INCLUDED

#include <vector>

namespace CaDiCaL {

class Clause;
using namespace std;

typedef cector<Clause*> Occs;

inline void shrink_occs (Occs & os) { os.shrink (); }
inline void erase_occs (Occs & os) { os.resize (0); os.shrink (); }

typedef Occs::iterator occs_iterator;
typedef Occs::const_iterator const_occs_iterator;

};

#endif
