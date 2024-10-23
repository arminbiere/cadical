// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2013 Stefan Kupferschmid
// Copyright 2023 Florian Pollitt
// Copyright 2023 Tobias Faller

#ifndef _craigtracer_hpp_INCLUDED
#define _craigtracer_hpp_INCLUDED

#include "cadical.hpp"
#include "tracer.hpp"

#include <iostream>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

namespace CaDiCraig {

class Aig;
struct CraigData;

enum class CraigCnfType : uint8_t { NONE, CONSTANT0, CONSTANT1, NORMAL };

enum class CraigConstruction : uint8_t {
  NONE = 0,
  SYMMETRIC = 1,
  ASYMMETRIC = 2,
  DUAL_SYMMETRIC = 4,
  DUAL_ASYMMETRIC = 8,
  ALL = 15
};

enum class CraigInterpolant : uint8_t {
  NONE,
  SYMMETRIC,
  ASYMMETRIC,
  DUAL_SYMMETRIC,
  DUAL_ASYMMETRIC,
  INTERSECTION,
  UNION,
  SMALLEST,
  LARGEST
};

CraigConstruction operator| (const CraigConstruction &first,
                             const CraigConstruction &second);

enum class CraigVarType : uint8_t { A_LOCAL, B_LOCAL, GLOBAL };

std::string to_string (const CraigVarType &var_type);
std::ostream &operator<< (std::ostream &out, const CraigVarType &var_type);

enum class CraigClauseType : uint8_t { A_CLAUSE, B_CLAUSE, L_CLAUSE };

std::string to_string (const CraigClauseType &clause_type);
std::ostream &operator<< (std::ostream &,
                          const CraigClauseType &clause_type);

class CraigTracer : public CaDiCaL::Tracer {
public:
  CraigTracer ();
  virtual ~CraigTracer ();

  // ====== BEGIN CRAIG INTERFACE ==========================================

  // Add variable of A, B or G type. This has to be called before
  // adding clauses using the variables when Craig interpolation is enabled.
  // - A_LOCAL
  // - B_LOCAL
  // - GLOBAL
  //
  //   require (VALID)
  //
  void label_variable (int id, CraigVarType variable_type);

  // Add clause type of A or B. This has to be called right
  // before adding the respective clause that this type applies to.
  // - A_CLAUSE
  // - B_CLAUSE
  //
  //   require (VALID)
  //
  void label_clause (int id, CraigClauseType clause_type);

  // Set constraint type to A or B. This has to be done before calling
  // solve.
  // - A_CLAUSE
  // - B_CLAUSE
  //
  //   require (VALID)
  //
  void label_constraint (CraigClauseType clause_type);

  // A bit field that configures the Craig interpolant bases to be built.
  // The following interpolant bases can be built:
  // - SYMMETRIC
  // - ASYMMETRIC
  // - DUAL_SYMMETRIC
  // - DUAL_ASYMMETRIC
  //
  //   require (CONFIGURING)
  //   ensure (CONFIGURING)
  //
  void set_craig_construction (CraigConstruction craig_construction);

  // Builds the Craig interpolant specified and writes the result
  // to the output vector. Required Tseitin variables for CNF creation
  // will start from the tseitin_offset provided.
  // The following interpolants are available:
  // - NONE
  // - SYMMETRIC (requires base SYMMETRIC)
  // - ASYMMETRIC (requires base ASYMMETRIC)
  // - DUAL_SYMMETRIC (requires base DUAL_SYMMETRIC)
  // - DUAL_ASYMMETRIC (requires base DUAL_ASYMMETRIC)
  // - INTERSECTION (of selected interpolant bases)
  // - UNION (of selected interpolant bases)
  // - SMALLEST (of selected interpolant bases)
  // - LARGEST (of selected interpolant bases)
  //
  // Returns the resulting CNF type.
  // The result can be NONE when either no Interpolant was requested
  // or if the construction of the craig interpolant is not enabled.
  // The NORMAL type CNF contains a unit clause with the trigger
  // for the Craig interpolant as the last clause.
  // The following CNF types can be returned by the function:
  // - NONE
  // - CONSTANT0 (CNF is constant false)
  // - CONSTANT1 (CNF is constant true)
  // - NORMAL (CNF is not constant)
  //
  //   require (UNSATISFIED)
  //
  CraigCnfType create_craig_interpolant (CraigInterpolant interpolant,
                                         std::vector<std::vector<int>> &cnf,
                                         int &tseitin_offset);

  // ====== END CRAIG INTERFACE ============================================

  void add_original_clause (uint64_t id, bool redundant,
                            const std::vector<int> &c,
                            bool restore) override;
  void
  add_derived_clause (uint64_t id, bool redundant,
                      const std::vector<int> &c,
                      const std::vector<uint64_t> &proof_chain) override;
  void
  add_assumption_clause (uint64_t id, const std::vector<int> &c,
                         const std::vector<uint64_t> &proof_chain) override;
  void delete_clause (uint64_t id, bool redundant,
                      const std::vector<int> &c) override;

  void add_assumption (int lit) override;
  void add_constraint (const std::vector<int> &c) override;
  void reset_assumptions () override;
  void conclude_unsat (CaDiCaL::ConclusionType conclusion,
                       const std::vector<uint64_t> &proof_chain) override;

private:
  CraigData *create_interpolant_for_assumption (int literal);
  CraigData *create_interpolant_for_clause (const std::vector<int> &c,
                                            CraigClauseType t);
  void extend_interpolant_with_resolution (CraigData &result, int literal,
                                           const CraigData &craig_data);
  bool is_construction_enabled (CraigConstruction construction);
  void clear_craig_interpolant ();
  bool has_craig_interpolant ();

  uint8_t mark_literal (int literal);
  void unmark_all ();

  std::set<int> assumptions;
  std::vector<int> constraint;
  std::vector<uint64_t> assumption_clauses;

  std::vector<int> marked_history;
  std::unordered_map<int, uint8_t> marked_lits;

  int craig_clause_current_id;
  std::unordered_map<int, CraigVarType> craig_var_labels;
  std::unordered_map<int, CraigClauseType> craig_clause_labels;
  CraigClauseType craig_constraint_label;

  std::vector<std::vector<int>> craig_clauses;
  std::vector<CraigData *> craig_interpolants;

  CraigConstruction craig_construction;
  size_t craig_id;
  CraigData *craig_interpolant;

  Aig *craig_aig_sym;
  Aig *craig_aig_asym;
  Aig *craig_aig_dual_sym;
  Aig *craig_aig_dual_asym;
};

} // namespace CaDiCraig

#endif
