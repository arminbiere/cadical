#include "../../src/cadical.hpp"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <cassert>
#include <cstdlib>
#include <string>

extern "C" {
#include <sys/types.h>
#include <unistd.h>
}

using namespace CaDiCaL;
using namespace std;

#include "../../src/checker.hpp"
#include "../../src/file.hpp"
#include "../../src/frattracer.hpp"
#include "../../src/lratchecker.hpp"
#include "../../src/lrattracer.hpp"
#include "../../src/testing.hpp"
#include "../../src/tracer.hpp"

#define LOG(...) \
  do { \
  } while (0)

// This is the example from the header file

int main () {

  Solver *solver = new Solver;
  Internal *internal = Testing (solver).internal ();

  char lrat_proof_path[128];
  char frat_proof_path[128];
  char veripb_proof_path[128];

  const char *prefix = "/tmp/cadical-api-test-example-tracer";
  size_t pid = (size_t) getpid ();

  snprintf (lrat_proof_path, 128, "%s-%zu-lrat.proof", prefix, pid);
  snprintf (frat_proof_path, 128, "%s-%zu-frat.proof", prefix, pid);
  snprintf (veripb_proof_path, 128, "%s-%zu-veripb.proof", prefix, pid);

  File *f1 = File::write (internal, lrat_proof_path);
  File *f2 = File::write (internal, frat_proof_path);

  InternalTracer *t1 = new LratChecker (internal);
  InternalTracer *t2 = new Checker (internal);
  FileTracer *ft1 = new LratTracer (internal, f1, 0);
  FileTracer *ft2 = new FratTracer (internal, f2, 0, 0);
  StatTracer *st1 = new LratChecker (internal);
  StatTracer *st2 = new Checker (internal);

  // ------------------------------------------------------------------

  solver->connect_proof_tracer (t1, 1);
  solver->connect_proof_tracer (t2, 0);
  solver->connect_proof_tracer (ft1, 1);
  solver->set ("veripb", 4);
  solver->trace_proof (veripb_proof_path);
  solver->connect_proof_tracer (ft2, 0, 1);
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

  delete t1;
  delete ft1;
  delete st1;
  delete solver;

  unlink (lrat_proof_path);
  unlink (frat_proof_path);
  unlink (veripb_proof_path);

  return 0;
}
