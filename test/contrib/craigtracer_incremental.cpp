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

  tracer->label_variable (1, CaDiCraig::CraigVarType::A_LOCAL);
  tracer->label_variable (2, CaDiCraig::CraigVarType::B_LOCAL);
  tracer->label_variable (3, CaDiCraig::CraigVarType::GLOBAL);
  tracer->label_clause (1, CaDiCraig::CraigClauseType::A_CLAUSE);
  tracer->label_clause (2, CaDiCraig::CraigClauseType::B_CLAUSE);
  solver->add (1);
  solver->add (0);
  solver->add (2);
  solver->add (0);

  // ------------------------------------------------
  // A side is UNSATISFIABLE => Craig interpolant is CONSTANT0
  solver->assume (-1);
  assert (solver->solve () == CaDiCaL::Status::UNSATISFIABLE);

  int next_var = 2;
  std::vector<std::vector<int>> clauses;
  CaDiCraig::CraigCnfType result = tracer->create_craig_interpolant (
      CaDiCraig::CraigInterpolant::ASYMMETRIC, clauses, next_var);
  assert (result == CaDiCraig::CraigCnfType::CONSTANT0);
  assert (clauses == std::vector<std::vector<int>>{{}});
  assert (next_var == 2);

  // ------------------------------------------------
  // B side is UNSATISFIABLE
  solver->assume (-2);
  assert (solver->solve () == CaDiCaL::Status::UNSATISFIABLE);

  result = tracer->create_craig_interpolant (
      CaDiCraig::CraigInterpolant::ASYMMETRIC, clauses, next_var);
  assert (result == CaDiCraig::CraigCnfType::CONSTANT1);
  assert (clauses == std::vector<std::vector<int>>{});
  assert (next_var == 2);

  // ------------------------------------------------
  tracer->label_clause (3, CaDiCraig::CraigClauseType::A_CLAUSE);
  tracer->label_constraint (CaDiCraig::CraigClauseType::B_CLAUSE);
  solver->add (-1);
  solver->add (3);
  solver->add (0);
  solver->constrain (-2);
  solver->constrain (-3);
  solver->constrain (0);
  assert (solver->solve () == CaDiCaL::Status::UNSATISFIABLE);

  result = tracer->create_craig_interpolant (
      CaDiCraig::CraigInterpolant::ASYMMETRIC, clauses, next_var);
  assert (result == CaDiCraig::CraigCnfType::NORMAL);
  assert (clauses == std::vector<std::vector<int>>{{3}});
  assert (next_var == 2);

  solver->disconnect_proof_tracer (tracer);
  delete tracer;
  delete solver;

  return 0;
}
