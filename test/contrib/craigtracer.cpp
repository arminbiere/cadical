#include "../../contrib/craigtracer.hpp"
#include "../../src/cadical.hpp"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <cassert>
#include <vector>

int main () {
  CaDiCaL::Solver *solver = new CaDiCaL::Solver ();
  CaDiCraig::CraigTracer *tracer = new CaDiCraig::CraigTracer ();
  solver->connect_proof_tracer (tracer, true);
  tracer->set_craig_construction (CaDiCraig::CraigConstruction::ASYMMETRIC);

  tracer->label_variable (1, CaDiCraig::CraigVarType::GLOBAL);
  tracer->label_clause (1, CaDiCraig::CraigClauseType::A_CLAUSE);
  tracer->label_clause (2, CaDiCraig::CraigClauseType::B_CLAUSE);
  solver->add (-1);
  solver->add (0);
  solver->add (1);
  solver->add (0);
  assert (solver->solve () == CaDiCaL::Status::UNSATISFIABLE);

  int next_var = 2;
  std::vector<std::vector<int>> clauses;
  CaDiCraig::CraigCnfType result = tracer->create_craig_interpolant (
      CaDiCraig::CraigInterpolant::ASYMMETRIC, clauses, next_var);
  assert (result == CaDiCraig::CraigCnfType::NORMAL);
  assert (clauses == std::vector<std::vector<int>>{{-1}});
  assert (next_var == 2);

  solver->disconnect_proof_tracer (tracer);
  delete tracer;
  delete solver;

  return 0;
}
