#include "../../src/cadical.hpp"

#include <iostream>

#ifdef NDEBUG
#undef NDEBUG
#endif

extern "C" {
#include <assert.h>
}

class Wrapper : CaDiCaL::Learner {
  CaDiCaL::Solver * solver;
  std::vector<int> clause;
public:
  unsigned clauses;
  Wrapper (CaDiCaL::Solver * s) : solver (s), clauses (0) { solver->connect_learner (this); }
  ~Wrapper () { solver->disconnect_learner (); }
  bool learning (int size) { (void) size; return true; }
  void learn (int lit) {
    if (lit) clause.push_back (lit);
    else {
      std::cout << "solver[" << ((void*) solver) << "] imported clause of size "
                << clause.size () << ':';
      for (auto lit : clause)
	std::cout << ' ' << lit;
      std::cout << std::endl << std::flush;
      clause.clear ();
      clauses++;
    }
  }
};

static void formula (CaDiCaL::Solver & solver) {
  for (int r = -1; r < 2; r += 2)
    for (int s = -1; s < 2; s += 2)
      for (int t = -1; t < 2; t += 2)
	solver.add (r * 1), solver.add (s * 2), solver.add (t * 3),
	solver.add (0);
}

int main () {
  CaDiCaL::Solver ping, pong;
  ping.set ("log", 1), pong.set ("log", 1);
  Wrapper wing (&ping), wong (&pong);
  formula (ping), formula (pong);
  int a = ping.solve ();
  std::cout << "ping returns " << a << std::endl;
  std::cout << "wong imported " << wing.clauses << " clauses" << std::endl;
  int b = pong.solve ();
  std::cout << "pong returns " << b << std::endl;
  std::cout << "wing imported " << wing.clauses << " clauses" << std::endl;
  assert (a == b), assert (a == 20);
  assert (wing.clauses == wong.clauses);
  assert (wing.clauses > 3);
  return 0;
}
