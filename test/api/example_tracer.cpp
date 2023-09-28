#include "../../src/cadical.hpp"
#ifdef NDEBUG
#undef NDEBUG
#endif
#include <cassert>
#include <cstdlib>
#include <string>

using namespace CaDiCaL;
using namespace std;
#include "../../src/checker.hpp"
#include "../../src/file.hpp"
#include "../../src/frattracer.hpp"
#include "../../src/lratchecker.hpp"
#include "../../src/lrattracer.hpp"
#include "../../src/tracer.hpp"

#define LOG(...) \
  do { \
  } while (0)

// This is the example from the header file

int main () {

  Solver *solver = new Solver;

  File *f1 = File::write (0, "/tmp/lrat.proof");
  File *f2 = File::write (0, "/tmp/frat.proof");

  InternalTracer *t1 = new LratChecker (0);
  InternalTracer *t2 = new Checker (0);
  FileTracer *ft1 = new LratTracer (0, f1, 0);
  FileTracer *ft2 = new FratTracer (0, f2, 0, 0);
  StatTracer *st1 = new LratChecker (0);
  StatTracer *st2 = new Checker (0);

  // ------------------------------------------------------------------

  solver->connect_proof_tracer (t1, 1);
  solver->connect_proof_tracer (t2, 0);
  solver->connect_proof_tracer (ft1, 1);
  solver->set ("veripb", 4);
  solver->trace_proof ("/tmp/veripb.proof");
  solver->connect_proof_tracer (ft2, 0);
  solver->connect_proof_tracer (st1, 1);
  solver->connect_proof_tracer (st2, 0);

  solver->add (1);
  solver->add (2);
  solver->add (0);

  solver->add (-1);
  solver->add (-2);
  solver->add (0);

  solver->add (1);
  solver->add (-2);
  solver->add (0);

  solver->constrain (-1);
  solver->constrain (2);
  solver->constrain (0);

  solver->solve ();

  solver->failed (1);
  solver->conclude ();

  solver->add (-1);
  solver->add (2);
  solver->add (0);

  solver->solve ();

  solver->conclude ();

  // tracers that are not disconnected are deleted when deleting solver
  //
  solver->disconnect_proof_tracer (t1);
  solver->disconnect_proof_tracer (ft1);
  solver->disconnect_proof_tracer (st1);

  // ------------------------------------------------------------------

  delete solver;
  delete t1;
  delete ft1;
  delete st1;

  return 0;
}
