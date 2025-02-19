#include "../../src/cadical.hpp"
#include <iostream>
#include <set>
#include <string>

extern "C" {
#include <assert.h>
}

CaDiCaL::Solver *solver = new CaDiCaL::Solver ();

void check_test_case (const std::vector<int> &constrain,
                      const std::vector<int> &assumptions,
                      const int expected_result) {
  std::cout << "Test case: ";
  std::cout << "<";
  if (!constrain.empty ()) {
    for (auto const &lit : constrain) {
      solver->constrain (lit);
      std::cout << " " << lit;
    }
    solver->constrain (0);
  }

  std::cout << " >[";
  if (!assumptions.empty ()) {
    for (auto const &lit : assumptions) {
      solver->assume (lit);
      std::cout << " " << lit;
    }
  }
  std::cout << " ] -> ";

  int res = solver->propagate ();
  std::cout << res << " ";

  assert (res == expected_result);
  (void) expected_result;

  // Check if returned set is subset of the expected result

  if (res == 10) {
    std::cout << " (model: [";

    std::vector<int> model;
    for (int idx = 1; idx <= 3; idx++) {
      int lit = solver->val (idx);
      model.push_back (lit);
      std::cout << " " << lit;
    }
    std::cout << " ])" << std::endl;

    if (!constrain.empty ()) {
      for (auto const &lit : constrain) {
        solver->constrain (lit);
      }
      solver->constrain (0);
    }
    if (!assumptions.empty ()) {
      for (auto const &lit : assumptions) {
        solver->assume (lit);
      }
    }
    for (auto const &lit : model) {
      solver->assume (lit);
    }

    res = solver->solve ();
    assert (res == 10);

  } else if (res == 0) {
    std::cout << " (implicants: [";
    std::vector<int> implicants;
    solver->get_entrailed_literals (implicants);
    // Check that every propagation holds
    for (auto const &lit : implicants) {
      std::cout << " " << lit;
      for (auto const &lit : assumptions)
        solver->assume (lit);
      if (!constrain.empty ()) {
        for (auto const &lit : constrain)
          solver->constrain (lit);
        solver->constrain (0);
      }

      solver->assume (-lit);

      res = solver->solve ();
      assert (res == 20);
    }
    std::cout << " ])" << std::endl;

  } else {
    std::cout << " (core: [";
    assert (res == 20);
    std::set<int> core;
    for (auto const &lit : assumptions) {
      if (solver->failed (lit)) {
        core.insert (lit);
        std::cout << " " << lit;
      }
    }
    std::cout << " ])" << std::endl;

    // Rerun call with the core-subset of assumptions
    if (!constrain.empty ()) {
      for (auto const &lit : constrain)
        solver->constrain (lit);
      solver->constrain (0);
    }
    for (auto const &lit : core) {
      solver->assume (lit);
    }

    res = solver->solve ();
    assert (res == 20);
  }
}

// Taken from incproof.cpp test file
static std::string path (const char *name) {
  const char *prefix = getenv ("CADICALBUILD");
  std::string res = prefix ? prefix : ".";
  res += "/test-api-propagate-";
  res += name;
  return res;
}

int main () {
  // ------------------------------------------------------------------
  // Encode Problem and check without assumptions.

  enum { TIE = 1, SHIRT = 2, HAT = 3, SHOES = 4, SLIPPERS = 5 };

  solver->set ("binary", 0);
  solver->set ("lidrup", 1);
  solver->trace_proof (path ("propagate_assumptions.lidrup").c_str ());
  solver->set ("flushproof", 1);

  solver->add (-TIE), solver->add (SHIRT), solver->add (0);
  solver->add (TIE), solver->add (SHIRT), solver->add (0);
  solver->add (-TIE), solver->add (-SHIRT), solver->add (0);

  std::vector<int> constrain;
  std::vector<int> assumptions;
  std::set<int> result;

  // ------------------------------------------------------------------
  // Check different test cases, signature:
  // ({literals of constrain},{assumption literals},expected results)

  check_test_case ({}, {}, 0);

  check_test_case ({HAT}, {}, 0);

  check_test_case ({HAT}, {-HAT}, 20);

  check_test_case ({}, {TIE, -TIE}, 20);

  check_test_case ({}, {TIE}, 20);

  check_test_case ({}, {-TIE}, 0);

  check_test_case ({}, {SHIRT}, 0);
  check_test_case ({}, {-SHIRT, HAT}, 20);

  check_test_case ({}, {SHIRT, TIE}, 20);
  check_test_case ({}, {SHIRT, -TIE}, 0);
  check_test_case ({}, {-SHIRT, TIE}, 20);
  check_test_case ({}, {-SHIRT, -TIE}, 20);
  check_test_case ({HAT}, {SHIRT, -TIE, HAT}, 10);

  // Check when root-level propagation satisfies
  solver->add (-TIE), solver->add (0);
  solver->add (SHIRT), solver->add (0);
  solver->add (HAT), solver->add (0);

  check_test_case ({HAT}, {SHIRT, -TIE, HAT}, 10);
  check_test_case ({}, {}, 10);

  // Check when root-level propagation falsifies
  solver->add (-HAT), solver->add (0);
  check_test_case ({}, {}, 20);

  solver->close_proof_trace (true);
  delete solver;

  // Check when last level propagation is needed for conflict detection
  solver = new CaDiCaL::Solver ();

  solver->add (SHOES), solver->add (SLIPPERS), solver->add (0);
  solver->add (-SHOES), solver->add (-SLIPPERS), solver->add (0);

  solver->add (-HAT), solver->add (SLIPPERS), solver->add (0);
  solver->add (-TIE), solver->add (SHIRT), solver->add (0);
  solver->add (-6), solver->add (7), solver->add (0);
  solver->add (-6), solver->add (-8), solver->add (0);
  solver->add (-7), solver->add (-SHIRT), solver->add (-TIE),
      solver->add (8), solver->add (0);

  check_test_case ({}, {HAT, TIE, 6}, 20);

  return 0;
}
