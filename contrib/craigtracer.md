# Introduction

The `CraigTracer` builds Craig interpolants via the CaDiCaL tracer interface.
The tracer interface notifies about proof resolution steps which the tracer
uses to build partial interpolants based on predefined construction rules.
Construction of symmetric and asymmetric Craig interpolants is supported.
Internally the interpolants are constructed as And-Inverter-Graph (AIG)
and a Tseitin transformation converts them into a Conjunctive Normal Form (CNF).

## Attaching the Tracer

Attach / detach the `CraigTracer` to the CaDiCaL solver via the
`connect_proof_tracer` and `disconnect_proof_tracer` methods.
The tracer requires antecedents. Therefore it has to be attached with `true`
as second argument. The partial Craig interpolant construction has to be
configured before any clauses are added to the solver.

```cpp
CaDiCaL::Solver solver;
CaDiCraig::CraigTracer tracer;
solver.connect_proof_tracer (&tracer, true);
tracer.set_craig_construction (CaDiCraig::CraigConstruction::ASYMMETRIC);

solver.add (...);
solver.solve ();

solver.disconnect_proof_tracer (&tracer);
```

## Labelling Variables and Clauses

Clauses and variables have to be labelled before they are added to the solver.
The methods `label_variable` and `label_clause` provide that and use indices
starting from 1 to assign variables / clauses.

Label variables via `label_variable` and the following types:
- `CaDiCraig::A_LOCAL`
- `CaDiCraig::B_LOCAL`
- `CaDiCraig::GLOBAL`

Label clauses via `label_clause` and the following types:
- `CaDiCraig::A_CLAUSE`
- `CaDiCraig::B_CLAUSE`

```cpp
CaDiCaL::Solver solver;
CaDiCraig::CraigTracer tracer;
solver.connect_proof_tracer (&tracer, true);
tracer.set_craig_construction (CaDiCraig::CraigConstruction::ASYMMETRIC);

tracer.label_variable (1, CaDiCraig::CraigVarType::GLOBAL);
tracer.label_clause (1, CaDiCraig::CraigClauseType::A_CLAUSE);
tracer.label_clause (2, CaDiCraig::CraigClauseType::B_CLAUSE);
solver.add (-1); solver.add (0);
solver.add (1); solver.add (0);
solver.solve ();

solver.disconnect_proof_tracer (&tracer);
```

## Getting Craig Interpolants

After CaDiCaL returns UNSATISFIABLE from its solve method a Craig interpolant
can be built via the `create_craig_interpolant` method. This method converts
the AIG containing partial interpolants into a final Craig interpolant in CNF
form using the Tseitin transformation.

Multiple partial interpolants can be built during solving to later be used
for building a final interpolant.
- `CaDiCraig::SYMMETRIC`
- `CaDiCraig::ASYMMETRIC`
- `CaDiCraig::DUAL_SYMMETRIC`
- `CaDiCraig::DUAL_ASYMMETRIC`

The following final interpolants are implemented. The INTERSECTION, UNION,
SMALLEST and LARGEST interpolants are based on all the enabled partial
interpolants.

- `CaDiCraig::NONE`
- `CaDiCraig::SYMMETRIC` (requires partial interpolant SYMMETRIC)
- `CaDiCraig::ASYMMETRIC` (requires partial interpolant ASYMMETRIC)
- `CaDiCraig::DUAL_SYMMETRIC` (requires partial interpolant DUAL_SYMMETRIC)
- `CaDiCraig::DUAL_ASYMMETRIC` (requires partial interpolant DUAL_ASYMMETRIC)
- `CaDiCraig::INTERSECTION` (of selected partial interpolants)
- `CaDiCraig::UNION` (of selected partial interpolants)
- `CaDiCraig::SMALLEST` (of selected partial interpolants)
- `CaDiCraig::LARGEST` (of selected partial interpolants)

The `create_craig_interpolant` method returns the CNF that has been created.
A CNF of type NORMAL denotes that a Tseitin transformation has been applied.
CONST0 and CONST1 are returned if the AIG is constant. The NONE type
is returned when CaDiCaL provided a result different than UNSATISFIABLE
or when the required partial interpolants are not enabled.

- `CaDiCraig::NONE`
- `CaDiCraig::CONSTANT0` (CNF is constant false)
- `CaDiCraig::CONSTANT1` (CNF is constant true)
- `CaDiCraig::NORMAL` (CNF is not constant)

```cpp
CaDiCaL::Solver solver;
CaDiCraig::CraigTracer tracer;
solver.connect_proof_tracer (&tracer, true);
tracer.set_craig_construction (CaDiCraig::CraigConstruction::ASYMMETRIC);

tracer.label_variable (...);
tracer.label_clause (...);
solver.add (...);

if (solver.solve () == CaDiCaL::Status::UNSATISFIABLE) {
  // Indices of Tseitin variables that are used when converting the
  // Craig interpolant AIG to a CNF. The end_variable parameter
  // is updated by the create_craig_interpolant method.
  int first_variable = solver.vars () + 1;
  int end_variable = first_variable;
  std::vector<std::vector<int>> interpolant;
  CaDiCraig::CraigCnfType result = tracer.create_craig_interpolant (
    CaDiCraig::CraigInterpolant::ASYMMETRIC, interpolant, end_variable);

  // Printing created Tseitin variables:
  for (int i = first_variable; i < end_variable; i++) {
    printf("Tseiting variable %d\n", i);
  }

  // Printing created Craig interpolant clauses:
  printf("Interpolant CNF type is %s", to_string(result));
  for (int i = 0; i < clauses.size(); i+++) {
    printf("Interpolant clause (");
    for (int j = 0; j < clauses[i].size(); j++) {
      if (j != 0) printf(", ");
      printf("%d", clauses[i][j]);
    }
    printf(")");
  }
}

solver.disconnect_proof_tracer (&tracer);
```

## Building multiple Interpolants

Multiple partial interpolant AIGs can be built automatically. These partial
interpolants can be transformed into CNFs independently depending on
the present use-case.

```cpp
CaDiCaL::Solver solver;
CaDiCraig::CraigTracer tracer;
solver.connect_proof_tracer (&tracer, true);
tracer.set_craig_construction (
  CaDiCraig::CraigConstruction::ASYMMETRIC
  | CaDiCraig::CraigConstruction::DUAL_ASYMMETRIC);

tracer.label_variable (...);
tracer.label_clause (...);
solver.add (...);

if (solver.solve () == CaDiCaL::Status::UNSATISFIABLE) {
  std::vector<std::vector<int>> cnf_asym;
  tracer.create_craig_interpolant (
    CaDiCraig::CraigInterpolant::ASYMMETRIC, cnf_asym, ...);

  std::vector<std::vector<int>> cnf_dual;
  tracer.create_craig_interpolant (
    CaDiCraig::CraigInterpolant::DUAL_ASYMMETRIC, cnf_dual, ...);

  std::vector<std::vector<int>> cnf_union;
  tracer.create_craig_interpolant (
    CaDiCraig::CraigInterpolant::UNION, cnf_union, ...);

  std::vector<std::vector<int>> cnf_interst;
  tracer.create_craig_interpolant (
    CaDiCraig::CraigInterpolant::INTERSECTION, cnf_interst, ...);
}

solver.disconnect_proof_tracer (&tracer);
```

## Incremental solving with interpolation

The Craig tracer supports handling assumptions and constraints.
Assumptions are treated like equivalent temporary unit clauses with a
clause label according to the variable label (`label_variable`).
Global variables are handled like a B_CLAUSE.

- Assuming a `A_LOCAL` variable is equivalent to a temporary `A_CLAUSE` clause.
- Assuming a `B_LOCAL` variable is equivalent to a temporary `B_CLAUSE` clause.
- Assuming a `GLOBAL` variable is equivalent to a temporary `B_CLAUSE` clause.

The constraint is treated as a temporary clause.
It has to be explicitly labeled by calling `label_constraint`.

```cpp
CaDiCaL::Solver solver;
CaDiCraig::CraigTracer tracer;
solver.connect_proof_tracer (&tracer, true);
tracer.set_craig_construction (...);

tracer.label_variable (1, CaDiCraig::CraigVarType::A_LOCAL);
tracer.label_variable (2, CaDiCraig::CraigVarType::GLOBAL);
solver.assume (-1);
solver.assume (2);

tracer.label_constraint (CaDiCraig::CraigClauseType::A_CLAUSE);
solver.constrain (1);
solver.constrain (-2);
solver.constrain (0);

assert (solver.solve () == CaDiCaL::Status::UNSATISFIABLE);
tracer.create_craig_interpolant (...);

solver.disconnect_proof_tracer (&tracer);
```
