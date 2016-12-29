#ifndef QUIET
#ifndef _resources_hpp_INCLUDED
#define _resources_hpp_INCLUDED

namespace CaDiCaL {

// low-level time and memory usage functions

double process_time ();
size_t maximum_resident_set_size ();
size_t current_resident_set_size ();

};

#endif // ifndef _resources_hpp_INCLUDED
#endif // ifndef QUIET
