#ifndef _resources_hpp_INCLUDED
#define _resources_hpp_INCLUDED

namespace CaDiCaL {

double absolute_real_time ();
double absolute_process_time ();

uint64_t maximum_resident_set_size ();
uint64_t current_resident_set_size ();

int number_of_cores (Internal * internal = 0);
uint64_t memory_limit (Internal * internal = 0);

}

#endif // ifndef _resources_hpp_INCLUDED
