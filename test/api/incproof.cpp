#include "../../src/cadical.hpp"

#include <cstdlib>
#include <string>

using namespace std;
using namespace CaDiCaL;

static string path (const char *name) {
  const char *prefix = getenv ("CADICALBUILD");
  string res = prefix ? prefix : ".";
  res += "/test-api-apitrace-";
  res += name;
  return res;
}

int main () {

  {
    for (int lrat = 0; lrat < 2; lrat++) {
      Solver *solver = new Solver;
      solver->set ("log", 1);
      solver->set ("binary", 0);
      solver->set ("verbose", 3);
      solver->set ("flushproof", 1);
      solver->configure ("plain");
      solver->set ("elim", 1);
      solver->set ("lrat", lrat);
      solver->trace_proof (
          path (lrat ? "inctrace1.lrat" : "inctrace1.drup").c_str ());
      solver->clause (1, 2, 3);
      solver->simplify ();
      solver->clause (-1, -2, -3);
      solver->solve ();
      solver->close_proof_trace (true);
      delete solver;
    }
  }

  {
    for (int lrat = 0; lrat < 2; lrat++) {
      Solver *solver = new Solver;
      solver->set ("log", 1);
      solver->set ("binary", 0);
      solver->set ("verbose", 3);
      solver->set ("flushproof", 1);
      solver->configure ("plain");
      solver->set ("elim", 1);
      solver->set ("lrat", lrat);
      solver->trace_proof (
          path (lrat ? "inctrace2.lrat" : "inctrace2.drup").c_str ());
      for (int i = -1; i <= -1; i += 2)
        for (int j = -1; j <= 1; j += 2)
          for (int k = -1; k <= 1; k += 2)
            solver->clause (i * 1, j * 2, k * 3);
      solver->simplify ();
      for (int i = 1; i <= 1; i += 2)
        for (int j = -1; j <= 1; j += 2)
          for (int k = -1; k <= 1; k += 2)
            solver->clause (i * 1, j * 2, k * 3);
      solver->solve ();
      solver->close_proof_trace (true);
      delete solver;
    }
  }

  return 0;
}
