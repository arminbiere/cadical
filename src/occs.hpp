#ifndef _occs_h_INCLUDED
#define _occs_h_INCLUDED

#include <vector>


namespace CaDiCaL {

// Full occurrence lists used in a one-watch scheme for all clauses in
// subsumption checking and for irredundant clauses in variable elimination.

class Clause;
using namespace std;

typedef vector<Clause*> Occs;

inline void shrink_occs (Occs & os) { shrink_vector (os); }
inline void erase_occs (Occs & os) { erase_vector (os); }

typedef Occs::iterator occs_iterator;
typedef Occs::const_iterator const_occs_iterator;

};

#endif
