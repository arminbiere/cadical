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
  assumed = 0;
}


void Assumptions::reset_ilb (unsigned level) {
  if (level >= control.size ())
    return;
  assumed = control[level];
  // this does not hold here as we might have changed the assumptions
  // assert (assumed <= assumptions.size ());
  //
  control.resize (level + 1);
}

void Assumptions::decide () {
  assert (assumed <= assumptions.size ());
  assert (assumed > 0);
  control.push_back(assumed-1);
}

void Assumptions::backtrack (unsigned level) {
  if (level >= control.size ())
    return;
  if (assumed)
    assumed = control[level];
//assert (assumed <= assumptions.size ());
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


void Assumptions::pop () {
  assert (assumed > 0);
  --assumed;
};

void Assumptions::undo_all () {
  assumed = 0;
}

}