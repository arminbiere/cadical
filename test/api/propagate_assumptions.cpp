#include "../../src/cadical.hpp"
#include <iostream>
#include <set>

extern "C" {
#include <assert.h>
}

CaDiCaL::Solver *solver = new CaDiCaL::Solver ();

void check_test_case (const std::vector<int>& constrain,
                 const std::vector<int>& assumptions,
                 const int expected_result) {
  std::cout << "Test case: ";
  std::cout << "<";
  if (!constrain.empty()) {
    for (auto const& lit : constrain) {
      solver->constrain (lit);
      std::cout << " " << lit;
    }
    solver->constrain (0);
  }
  std::cout << " >";
  std::cout << "[";
  if (!assumptions.empty()) {  
    for (auto const& lit : assumptions) {
      solver->assume (lit);
      std::cout << " " << lit;
    }
  }
  std::cout << " ] -> ";

  std::vector<int> implicants;
  int res = solver->propagate (implicants);
  std::cout << res;

  assert (res == expected_result);

  
  

  // Check if returned set is subset of the expected result
  

  if (res == 10) {
    std::cout << " (model: [";
    if (!constrain.empty()) {
      for (auto const& lit : constrain) {
        solver->constrain (lit);
      }
      solver->constrain (0);
    }
    for (auto const& lit : implicants) {
      std::cout << " " << lit;
      solver->assume(lit);
    }
    std::cout << " ])" << std::endl;
    res = solver->solve();
    assert(res == 10);

  } else if (res == 0) {
    std::cout << " (implicants: [";
    // Check that every propagation holds
    for (auto const& lit : implicants) {
      std::cout << " " << lit;
      for (auto const& lit : assumptions) solver->assume (lit);
      if (!constrain.empty()) {
        for (auto const& lit : constrain) solver->constrain (lit);
        solver->constrain (0);
      }
      
      solver->assume(-lit);

      res = solver->solve ();
      assert (res == 20);
    
    }
    std::cout << " ])" << std::endl;
  
  } else {
    std::cout << " (core: [";
    assert(res == 20);
    std::set<int> core;
    for (auto const& lit : assumptions) {
      if (solver->failed(lit)) {
        core.insert(lit);
        std::cout << " " << lit;
      }
    }
    std::cout << " ])" << std::endl;


    // Rerun call with the core-subset of assumptions
    if (!constrain.empty()) {
      for (auto const& lit : constrain) solver->constrain (lit);
      solver->constrain (0);
    }
    for (auto const& lit : core) {
      solver->assume (lit);
    }

    res = solver->solve();
    assert(res == 20);
  }
}

int main () {
  // ------------------------------------------------------------------
  // Encode Problem and check without assumptions.

  enum { TIE = 1, SHIRT = 2, HAT = 3 };

  solver->add (-TIE), solver->add (SHIRT), solver->add (0);
  solver->add (TIE), solver->add (SHIRT), solver->add (0);
  solver->add (-TIE), solver->add (-SHIRT), solver->add (0);
  
  std::vector<int> constrain;
  std::vector<int> assumptions;
  std::set<int> result;

  // ------------------------------------------------------------------
  // Check different test cases, signature:
  // ({literals of constrain},{assumption literals},expected results)

  check_test_case({},{},0);
  
  check_test_case ({HAT},{},0);
  
  check_test_case ({HAT},{-HAT},20);

  check_test_case ({},{TIE,-TIE},20);

  check_test_case ({},{TIE},20);

  check_test_case ({},{-TIE},0);

  check_test_case ({},{SHIRT},0);
  check_test_case ({},{-SHIRT,HAT},20);

  check_test_case ({},{SHIRT,TIE},20);
  check_test_case ({},{SHIRT,-TIE},0);
  check_test_case ({},{-SHIRT,TIE},20);
  check_test_case ({},{-SHIRT,-TIE},20);
  check_test_case ({HAT},{SHIRT,-TIE,HAT},10);


  // Check when root-level propagation satisfies
  solver->add (-TIE), solver->add (0);
  solver->add (SHIRT), solver->add (0);
  solver->add (HAT), solver->add (0);
  
  check_test_case ({HAT},{SHIRT,-TIE,HAT},10);
  check_test_case ({},{},10);

  // Check when root-level propagation falsifies
  solver->add (-HAT), solver->add (0);
  check_test_case ({},{},20);
  
  delete solver;
  
  return 0;
}