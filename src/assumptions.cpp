#include "assumptions.hpp"

#include <cassert>

namespace CaDiCaL {

bool Assumptions::satisfied () {
 return assumed == assumptions.size (); 
}


void Assumptions::add (int a) {
  assert (std::find (assumptions.begin (), assumptions.end (), a) ==
          assumptions.end ());
  assumptions.push_back(a);
    
}

void Assumptions::clear () {
  assumptions.clear ();
  control.resize (1);
  assert (control[0] == 0);
  assumed = 0;
}

void Assumptions::decide () {
  assert (assumed <= assumptions.size ());
  control.push_back(assumed-1);
}

void Assumptions::backtrack (unsigned level) {
  if (level >= control.size ())
    return;
  assumed = control[level];
  assert (assumed <= assumptions.size ());
  control.resize (level + 1);
}


int Assumptions::next () {
  assert (assumed < assumptions.size ());
  return assumptions [assumed++];
}

size_t Assumptions::level () {
  return control.size () - 1;
}

size_t Assumptions::size () {
  return assumptions.size ();
}




}