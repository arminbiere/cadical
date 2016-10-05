#ifndef _signal_hpp_INCLUDED
#define _signal_hpp_INCLUDED

namespace CaDiCaL {
class Solver;
void reset_signal_handlers ();
void init_signal_handlers (Solver &);
};

#endif

