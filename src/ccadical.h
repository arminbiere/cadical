#ifndef _ccadical_h_INCLUDED
#define _ccadical_h_INCLUDED

// C wrapper for CaDiCaL's C++ API

typedef struct CCaDiCaL CCaDiCaL;

CCaDiCaL * ccadical_init ();
void ccadical_reset (CCaDiCaL *);

void ccadical_add (CCaDiCaL *, int lit);
int ccadical_sat (CCaDiCaL *);
int ccadical_deref (CCaDiCaL *, int lit);

#endif
