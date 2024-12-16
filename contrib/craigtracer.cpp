// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2013 Stefan Kupferschmid
// Copyright 2023 Florian Pollitt
// Copyright 2023 Tobias Faller

#include "craigtracer.hpp"

#include <algorithm>
#include <cassert>
#include <iostream>
#include <limits>
#include <map>
#include <stack>
#include <tuple>
#include <unordered_map>

namespace CaDiCraig {

// ----------------------------------------------------------------------------
// Minimal AIG implementation used for building Craig interpolants
// ----------------------------------------------------------------------------

class AigEdge {
public:
  AigEdge () : index (0) {}
  AigEdge (const AigEdge &other) : index (other.index) {}

  AigEdge &operator= (const AigEdge &other) {
    index = other.index;
    return *this;
  }
  AigEdge operator!() const { return AigEdge (index ^ 1); }

  bool operator== (const AigEdge &other) const {
    return index == other.index;
  }
  bool operator< (const AigEdge &other) const {
    return index < other.index;
  }
  bool operator> (const AigEdge &other) const {
    return index > other.index;
  }

  bool is_negated () const { return index & 1; }
  bool is_constant () const { return (index >> 1u) == 0; }

  friend class AigNode;
  friend class Aig;

private:
  explicit AigEdge (int index) : index (index) {}
  size_t get_node_index () const { return (index >> 1u) - 1; }

  int index;
};

class AigNode {
public:
  bool isAnd () const { return edge2.index != 0; }
  bool isVariable () const { return edge2.index == 0; }

  int get_variable () const { return edge1.index; }
  const AigEdge &get_edge1 () const { return edge1; }
  const AigEdge &get_edge2 () const { return edge2; }

  friend class Aig;

private:
  explicit AigNode (int _variable) : edge1 (_variable), edge2 (0) {}
  explicit AigNode (AigEdge _edge1, AigEdge _edge2)
      : edge1 (_edge1), edge2 (_edge2) {}

  AigEdge edge1;
  AigEdge edge2;
};

class Aig {
public:
  Aig () : nodes (), varHashMap (), andHashMap () {}

  static AigEdge get_true () { return AigEdge (0); }
  static AigEdge get_false () { return AigEdge (1); }

  void clear () {
    nodes.clear ();
    varHashMap.clear ();
    andHashMap.clear ();
  }
  AigEdge create_literal (int literal);
  AigEdge create_and (const AigEdge &edge1, const AigEdge &edge2);
  AigEdge create_or (const AigEdge &edge1, const AigEdge &edge2);
  AigEdge create_and (std::vector<AigEdge> edges);
  AigEdge create_or (std::vector<AigEdge> edges);

  CraigCnfType create_cnf (const AigEdge &root,
                           std::vector<std::vector<int>> &cnf,
                           int &nextFreeIndex) const;

private:
  AigEdge create_var (int variable);

  struct EdgePairHash {
    int operator() (const std::tuple<AigEdge, AigEdge> &edges) const {
      return (std::get<0> (edges).index << 16u) | std::get<1> (edges).index
                                                      << 0u;
    }
  };
  struct VarHash {
    int operator() (const int &variable) const { return variable; }
  };

  std::vector<AigNode> nodes;
  std::unordered_map<int, int, VarHash> varHashMap;
  std::unordered_map<std::tuple<AigEdge, AigEdge>, int, EdgePairHash>
      andHashMap;
};

AigEdge Aig::create_var (int variable) {
  // Try to check if there is a node for the literal already
  auto it = varHashMap.find (variable);
  if (it != varHashMap.end ()) {
    return AigEdge (it->second);
  }

  // Nodes 0 and 1 are constant nodes and reserved
  // and already factored into the index.
  nodes.emplace_back (AigNode (variable));
  varHashMap[variable] = (nodes.size () << 1u);
  return AigEdge (nodes.size () << 1u);
}

AigEdge Aig::create_literal (int literal) {
  auto edge = create_var (abs (literal));
  return (literal < 0) ? !edge : edge;
}

AigEdge Aig::create_and (const AigEdge &edge1, const AigEdge &edge2) {
  if (edge1 == get_false () || edge2 == get_false ())
    return get_false ();
  if (edge1 == get_true ())
    return edge2;
  if (edge2 == get_true ())
    return edge1;
  if (edge1 == edge2)
    return edge1;
  if (edge1 == !edge2)
    return get_false ();

  // Order edge indices to increase hit rate
  auto pair = (edge1 > edge2) ? std::make_tuple (edge2, edge1)
                              : std::make_tuple (edge1, edge2);
  auto it = andHashMap.find (pair);
  if (it != andHashMap.end ()) {
    return AigEdge (it->second);
  }

  // Lookup failed, create new node.
  // Nodes 0 and 1 are constant nodes and reserved
  // and already factored into the index.
  nodes.emplace_back (AigNode (edge1, edge2));
  andHashMap[pair] = (nodes.size () << 1u);
  return AigEdge (nodes.size () << 1u);
}

AigEdge Aig::create_and (std::vector<AigEdge> edges) {
  if (edges.empty ())
    return get_true ();
  if (edges.size () == 1u)
    return edges[0u];

  // Tree reduction of edges
  std::vector<AigEdge> tempEdges;
  while (edges.size () > 1u) {
    tempEdges.reserve ((edges.size () / 2u) + 1u);
    for (size_t index{0u}; index + 1u < edges.size (); index += 2u) {
      tempEdges.emplace_back (create_and (edges[index], edges[index + 1u]));
    }
    if (edges.size () & 1)
      tempEdges.emplace_back (edges.back ());

    edges = std::move (tempEdges);
    tempEdges.clear ();
  }

  return edges[0u];
}

AigEdge Aig::create_or (const AigEdge &edge1, const AigEdge &edge2) {
  return !create_and (!edge1, !edge2);
}

AigEdge Aig::create_or (std::vector<AigEdge> edges) {
  for (auto &edge : edges)
    edge = !edge;
  return !create_and (edges);
}

CraigCnfType Aig::create_cnf (const AigEdge &root,
                              std::vector<std::vector<int>> &cnf,
                              int &nextFreeIndex) const {
  // The AIG is constant => Handle this simple case.
  if (root.is_constant ()) {
    if (root == get_false ()) {
      cnf.push_back ({});
      return CraigCnfType::CONSTANT0;
    }
    return CraigCnfType::CONSTANT1;
  }

  // A fixed single literal => No Tseitin variables are required
  // and we can take a fast path without building an index.
  auto node = nodes[root.get_node_index ()];
  if (node.isVariable ()) {
    auto rootLiteral = node.get_variable () * (root.is_negated () ? -1 : 1);
    cnf.push_back ({rootLiteral});
    return CraigCnfType::NORMAL;
  }

  // Create index of pre-existing (external) variables.
  // This index is extended with Tseitin variables are required.
  std::map<size_t, int> node_to_var;
  for (size_t nodeIndex{0u}; nodeIndex < nodes.size (); nodeIndex++) {
    auto const &node = nodes[nodeIndex];
    if (node.isVariable ())
      node_to_var[nodeIndex] = node.get_variable ();
  }

  std::stack<size_t> pending{{root.get_node_index ()}};
  while (!pending.empty ()) {
    const auto nodeIndex = pending.top ();
    const auto &node = nodes[nodeIndex];

    // Check if node was already converted to Tseitin variable.
    auto it = node_to_var.find (nodeIndex);
    if (it != node_to_var.end ()) {
      pending.pop ();
      continue;
    }

    // Both edges have to be processed first.
    const auto &edge1 = node.get_edge1 ();
    const auto &edge2 = node.get_edge2 ();
    const size_t node1Index = edge1.get_node_index ();
    const size_t node2Index = edge2.get_node_index ();
    auto itNode1 = node_to_var.find (node1Index);
    auto itNode2 = node_to_var.find (node2Index);
    if (itNode1 == node_to_var.end ()) {
      pending.push (node1Index);
    } else if (itNode2 == node_to_var.end ()) {
      pending.push (node2Index);
    } else {
      // Edges have been processed, now do Tseiting transformation.
      // This node is guaranteed to not be a variable as they have been
      // inserted into the mapping at the start of this method.
      pending.pop ();

      const auto tseitinVar = nextFreeIndex++;
      node_to_var[nodeIndex] = tseitinVar;

      const auto litEdge1 =
          itNode1->second * (edge1.is_negated () ? -1 : 1);
      const auto litEdge2 =
          itNode2->second * (edge2.is_negated () ? -1 : 1);

      //  x = y * z <-> ( !x + y ) * ( !x + z ) * ( x + !y + !z )
      cnf.push_back ({-tseitinVar, litEdge1});
      cnf.push_back ({-tseitinVar, litEdge2});
      cnf.push_back ({tseitinVar, -litEdge1, -litEdge2});
    }
  }

  // Finally add the root literal to the CNF since the required tree
  // now has been built and the root Tseitin variable is accessible.
  cnf.push_back ({node_to_var[root.get_node_index ()] *
                  (root.is_negated () ? -1 : 1)});
  return CraigCnfType::NORMAL;
}

std::string to_string (const CraigVarType &var_type) {
  if (var_type == CraigVarType::A_LOCAL)
    return "A";
  if (var_type == CraigVarType::B_LOCAL)
    return "B";
  if (var_type == CraigVarType::GLOBAL)
    return "G";
  __builtin_unreachable ();
}

std::ostream &operator<< (std::ostream &out, const CraigVarType &var_type) {
  if (var_type == CraigVarType::A_LOCAL)
    out << "A";
  if (var_type == CraigVarType::B_LOCAL)
    out << "B";
  if (var_type == CraigVarType::GLOBAL)
    out << "G";
  return out;
}

std::string to_string (const CraigClauseType &clause_type) {
  if (clause_type == CraigClauseType::A_CLAUSE)
    return "A";
  if (clause_type == CraigClauseType::B_CLAUSE)
    return "B";
  if (clause_type == CraigClauseType::L_CLAUSE)
    return "L";
  __builtin_unreachable ();
}

std::ostream &operator<< (std::ostream &out,
                          const CraigClauseType &clause_type) {
  if (clause_type == CraigClauseType::A_CLAUSE)
    out << "A";
  if (clause_type == CraigClauseType::B_CLAUSE)
    out << "B";
  if (clause_type == CraigClauseType::L_CLAUSE)
    out << "L";
  return out;
}

struct CraigData {
  AigEdge partial_interpolant_sym;
  AigEdge partial_interpolant_asym;
  AigEdge partial_interpolant_dual_sym;
  AigEdge partial_interpolant_dual_asym;
  CraigClauseType clause_type;
  size_t craig_id;

  bool isPure () const { return clause_type != CraigClauseType::L_CLAUSE; }
};

// ----------------------------------------------------------------------------
// Computation of Craig interpolants
// ----------------------------------------------------------------------------

CraigTracer::CraigTracer ()
    : CaDiCaL::Tracer (), marked_history (), marked_lits (),
      craig_clause_current_id (1), craig_var_labels (),
      craig_clause_labels (),
      craig_constraint_label (CraigClauseType::L_CLAUSE), craig_clauses (),
      craig_interpolants (), craig_construction (CraigConstruction::NONE),
      craig_id (0), craig_interpolant (0), craig_aig_sym (new Aig ()),
      craig_aig_asym (new Aig ()), craig_aig_dual_sym (new Aig ()),
      craig_aig_dual_asym (new Aig ()) {}

CraigTracer::~CraigTracer () {
  for (auto *partial_interpolant : craig_interpolants)
    if (partial_interpolant)
      delete partial_interpolant;
  if (craig_interpolant)
    delete craig_interpolant;

  delete craig_aig_sym;
  delete craig_aig_asym;
  delete craig_aig_dual_sym;
  delete craig_aig_dual_asym;
}

void CraigTracer::set_craig_construction (
    CraigConstruction craig_construction) {
  assert (craig_clauses.empty ());
  this->craig_construction = craig_construction;
}

void CraigTracer::clear_craig_interpolant () { craig_interpolant = 0; }

bool CraigTracer::has_craig_interpolant () {
  return craig_interpolant != 0;
}

// C++11 version of insert_or_assign because it is only C++20
template <typename A>
void insert_or_assign (std::unordered_map<int, A> &craig_var_labels, int id,
                       A variable_type) {
  auto it = craig_var_labels.find (id);
  if (it != end (craig_var_labels))
    it->second = variable_type;
  else
    craig_var_labels.emplace (id, variable_type);
}
void CraigTracer::label_variable (int id, CraigVarType variable_type) {
  assert (id > 0);
  insert_or_assign<CraigVarType> (craig_var_labels, id, variable_type);
  insert_or_assign<uint8_t> (marked_lits, id, 0);
  // marked_lits.insert_or_assign (id, 0);
}

void CraigTracer::label_clause (int id, CraigClauseType clause_type) {
  assert (id > 0);
  insert_or_assign<CraigClauseType> (craig_clause_labels, id, clause_type);
}

void CraigTracer::label_constraint (CraigClauseType clause_type) {
  craig_constraint_label = clause_type;
}

void CraigTracer::add_original_clause (uint64_t id, bool redundant,
                                       const std::vector<int> &c,
                                       bool restore) {
  assert (id > 0);
  (void) redundant;

  if (restore) {
    craig_clauses[id - 1] = c;
    return;
  }

  int original_id = craig_clause_current_id++;
  assert (craig_clause_labels.find (original_id) !=
          craig_clause_labels.end ());
#ifndef NDEBUG
  for (auto &l : c) {
    assert (craig_var_labels.find (std::abs (l)) !=
            craig_var_labels.end ());
  }
#endif
  auto clause_label = craig_clause_labels.find (original_id)->second;
  auto *interpolant = create_interpolant_for_clause (c, clause_label);

  assert (craig_clauses.size () == id - 1);
  craig_clauses.push_back (c);
  craig_interpolants.push_back (interpolant);
}

void CraigTracer::add_derived_clause (
    uint64_t id, bool redundant, const std::vector<int> &c,
    const std::vector<uint64_t> &proof_chain) {
  assert (proof_chain.size () >= 1);
  (void) redundant;
#ifndef NDEBUG
  for (auto &clause : proof_chain)
    assert (craig_interpolants[clause - 1] != nullptr);
#endif
  // Mark literals of conflicting clause.
  for (auto &l : craig_clauses[proof_chain.back () - 1])
    mark_literal (l);

  // Find pivot literal of each clause that was resolved with
  // and extend Craig interpolant for it.
  auto *interpolant =
      new CraigData (*craig_interpolants[proof_chain.back () - 1]);
  for (int i = proof_chain.size () - 2; i >= 0; i--) {
    for (auto &l : craig_clauses[proof_chain[i] - 1]) {
      // Function mark_literal returns true if inverse literal was marked
      // before and marks literal l for the following resolvent literal
      // checks.
      if (!mark_literal (l))
        continue;

      extend_interpolant_with_resolution (
          *interpolant, -l, *craig_interpolants[proof_chain[i] - 1]);
    }
  }
  unmark_all ();
#ifndef NDEBUG
  assert (craig_clauses.size () == id - 1);
#else
  (void) id;
#endif
  craig_clauses.push_back (c);
  craig_interpolants.push_back (interpolant);
}

void CraigTracer::add_assumption_clause (
    uint64_t id, const std::vector<int> &c,
    const std::vector<uint64_t> &proof_chain) {
  CraigData *interpolant = 0;

  if (proof_chain.size () > 0) {
    // We have a resolution of multiple clauses and therefore reuse
    // the existing code to build our Craig interpolant.
    add_derived_clause (id, true, c, proof_chain);
    interpolant = craig_interpolants[id - 1];
  } else {
    assert (c.size () == 2);
    bool c0_is_assumption =
        (assumptions.find (-c[0]) != assumptions.end ());
    bool c1_is_assumption =
        (assumptions.find (-c[1]) != assumptions.end ());

    if (!c0_is_assumption || !c1_is_assumption) {
      int l = c0_is_assumption ? -c[1] : -c[0];
      assert (craig_clauses.size () == id - 1);
      craig_clauses.push_back ({l});
      craig_interpolants.push_back (create_interpolant_for_assumption (-l));
      assumption_clauses.push_back (id);
      return;
    }
  }

  for (auto &lit : c) {
    bool is_assumption = (assumptions.find (-lit) != assumptions.end ());
    if (!is_assumption) {
      continue;
    }

    auto *other = create_interpolant_for_assumption (-lit);
    if (interpolant) {
      extend_interpolant_with_resolution (*interpolant, lit, *other);
      delete other;
    } else {
      interpolant = other;
    }
  }

  if (proof_chain.size () == 0) {
    assert (craig_clauses.size () == id - 1);
    craig_clauses.push_back (c);
    craig_interpolants.push_back (interpolant);
  }
  assumption_clauses.push_back (id);
}

void CraigTracer::delete_clause (uint64_t id, bool redundant,
                                 const std::vector<int> &c) {
  (void) redundant;
  (void) c;

  assert (craig_clauses.size () >= id - 1);
  craig_clauses[id - 1].resize (0);
}

void CraigTracer::add_assumption (int lit) { assumptions.insert (lit); }

void CraigTracer::add_constraint (const std::vector<int> &c) {
  constraint = c;
}

void CraigTracer::reset_assumptions () {
  for (auto &id : assumption_clauses) {
    delete_clause (id, true, craig_clauses[id - 1]);
  }
  assumptions.clear ();
  constraint.clear ();
  assumption_clauses.clear ();
}

void CraigTracer::conclude_unsat (
    CaDiCaL::ConclusionType conclusion,
    const std::vector<uint64_t> &proof_chain) {
  if (craig_interpolant) {
    delete craig_interpolant;
    craig_interpolant = 0;
  }

  CraigData *interpolant = 0;
  if (conclusion == CaDiCaL::ConclusionType::CONFLICT) {
    // There is a single global conflict.
    // The proof_chain contains a single empty clause.
    // chain = (c1), c1 = {}
    assert (proof_chain.size () == 1);
    assert (craig_clauses[proof_chain[0] - 1].empty ());
    interpolant = new CraigData (*craig_interpolants[proof_chain[0] - 1]);
  } else if (conclusion == CaDiCaL::ConclusionType::ASSUMPTIONS) {
    // One or more constraints are responsible for the conflict.
    // The proof_chain contains a single clause with failing assumptions.
    // The interpolant of that clause already has been resolved with
    // assumption interpolants. chain = (c1), c1 = { -a1, -a2, -a3, ... }
    assert (proof_chain.size () == 1);
    assert (craig_clauses[proof_chain[0] - 1].size () > 0);
    interpolant = new CraigData (*craig_interpolants[proof_chain[0] - 1]);
  } else if (conclusion == CaDiCaL::ConclusionType::CONSTRAINT) {
    // The constraint clause is responsible for the conflict.

    // Mark literals of conflicting clause.
    for (auto &l : constraint)
      mark_literal (l);

    // Find pivot literal of each clause that was resolved with
    // and extend Craig interpolant for it.
    interpolant =
        create_interpolant_for_clause (constraint, craig_constraint_label);
    for (int i = proof_chain.size () - 1; i >= 0; i--) {
      for (auto &l : craig_clauses[proof_chain[i] - 1]) {
        // Function mark_literal returns true if inverse literal was marked
        // before and marks literal l for the following resolvent literal
        // checks.
        if (!mark_literal (l))
          continue;

        extend_interpolant_with_resolution (
            *interpolant, -l, *craig_interpolants[proof_chain[i] - 1]);
      }
    }

    unmark_all ();
  } else {
    assert (false); // No conclusion given!
  }

  craig_interpolant = interpolant;
}

CraigData *CraigTracer::create_interpolant_for_assumption (int literal) {
  assert (craig_var_labels.find (abs (literal)) != craig_var_labels.end ());

  CraigVarType varType = craig_var_labels[abs (literal)];
  if (varType == CraigVarType::A_LOCAL) {
    return new CraigData (
        {craig_aig_sym->get_false (), craig_aig_asym->get_false (),
         craig_aig_dual_sym->get_true (), craig_aig_dual_asym->get_false (),
         CraigClauseType::A_CLAUSE, craig_id++});
  } else if (varType == CraigVarType::B_LOCAL) {
    return new CraigData (
        {craig_aig_sym->get_true (), craig_aig_asym->get_true (),
         craig_aig_dual_sym->get_false (), craig_aig_dual_asym->get_true (),
         CraigClauseType::B_CLAUSE, craig_id++});
  } else if (varType == CraigVarType::GLOBAL) {
    return new CraigData ({craig_aig_sym->get_true (),
                           craig_aig_asym->get_true (),
                           craig_aig_dual_sym->get_false (),
                           craig_aig_dual_asym->get_false (),
                           CraigClauseType::L_CLAUSE, craig_id++});
  } else {
    assert (false); // Encountered invalid variable type!
    __builtin_unreachable ();
  }
}

CraigData *
CraigTracer::create_interpolant_for_clause (const std::vector<int> &clause,
                                            CraigClauseType clause_type) {
  auto result = new CraigData (
      {craig_aig_sym->get_true (), craig_aig_asym->get_true (),
       craig_aig_dual_sym->get_true (), craig_aig_dual_asym->get_true (),
       clause_type, craig_id++});

  if (is_construction_enabled (CraigConstruction::SYMMETRIC)) {
    if (clause_type == CraigClauseType::A_CLAUSE) {
      result->partial_interpolant_sym = craig_aig_sym->get_false ();
    } else if (clause_type == CraigClauseType::B_CLAUSE) {
      result->partial_interpolant_sym = craig_aig_sym->get_true ();
    }
  }
  if (is_construction_enabled (CraigConstruction::ASYMMETRIC)) {
    if (clause_type == CraigClauseType::A_CLAUSE) {
      std::vector<AigEdge> literals;
      for (size_t i = 0; i < clause.size (); ++i) {
        if (craig_var_labels[abs (clause[i])] == CraigVarType::GLOBAL) {
          literals.push_back (craig_aig_asym->create_literal (clause[i]));
        }
      }
      result->partial_interpolant_asym =
          craig_aig_asym->create_or (literals);
    } else if (clause_type == CraigClauseType::B_CLAUSE) {
      result->partial_interpolant_asym = craig_aig_asym->get_true ();
    }
  }
  if (is_construction_enabled (CraigConstruction::DUAL_SYMMETRIC)) {
    if (clause_type == CraigClauseType::A_CLAUSE) {
      result->partial_interpolant_dual_sym =
          craig_aig_dual_sym->get_true ();
    } else if (clause_type == CraigClauseType::B_CLAUSE) {
      result->partial_interpolant_dual_sym =
          craig_aig_dual_sym->get_false ();
    }
  }
  if (is_construction_enabled (CraigConstruction::DUAL_ASYMMETRIC)) {
    if (clause_type == CraigClauseType::A_CLAUSE) {
      result->partial_interpolant_dual_asym =
          craig_aig_dual_asym->get_false ();
    } else if (clause_type == CraigClauseType::B_CLAUSE) {
      std::vector<AigEdge> literals;
      for (size_t i = 0; i < clause.size (); ++i) {
        if (craig_var_labels[abs (clause[i])] == CraigVarType::GLOBAL) {
          literals.push_back (
              craig_aig_dual_asym->create_literal (-clause[i]));
        }
      }
      result->partial_interpolant_dual_asym =
          craig_aig_dual_asym->create_and (literals);
    }
  }

  return result;
}

void CraigTracer::extend_interpolant_with_resolution (
    CraigData &result, int literal, const CraigData &craig_data) {
  if (result.clause_type != craig_data.clause_type) {
    result.clause_type = CraigClauseType::L_CLAUSE;
  }

  if (is_construction_enabled (CraigConstruction::SYMMETRIC)) {
    if (craig_var_labels[abs (literal)] == CraigVarType::A_LOCAL) {
      result.partial_interpolant_sym =
          craig_aig_sym->create_or (result.partial_interpolant_sym,
                                    craig_data.partial_interpolant_sym);
    } else if (craig_var_labels[abs (literal)] == CraigVarType::B_LOCAL) {
      result.partial_interpolant_sym =
          craig_aig_sym->create_and (result.partial_interpolant_sym,
                                     craig_data.partial_interpolant_sym);
    } else {
      result.partial_interpolant_sym = craig_aig_sym->create_and (
          craig_aig_sym->create_or (
              result.partial_interpolant_sym,
              craig_aig_sym->create_literal (literal)),
          craig_aig_sym->create_or (
              craig_data.partial_interpolant_sym,
              craig_aig_sym->create_literal (-literal)));
    }
  }
  if (is_construction_enabled (CraigConstruction::ASYMMETRIC)) {
    if (craig_var_labels[abs (literal)] == CraigVarType::A_LOCAL) {
      result.partial_interpolant_asym =
          craig_aig_asym->create_or (result.partial_interpolant_asym,
                                     craig_data.partial_interpolant_asym);
    } else {
      result.partial_interpolant_asym =
          craig_aig_asym->create_and (result.partial_interpolant_asym,
                                      craig_data.partial_interpolant_asym);
    }
  }
  if (is_construction_enabled (CraigConstruction::DUAL_SYMMETRIC)) {
    if (craig_var_labels[abs (literal)] == CraigVarType::A_LOCAL) {
      result.partial_interpolant_dual_sym = craig_aig_dual_sym->create_and (
          result.partial_interpolant_dual_sym,
          craig_data.partial_interpolant_dual_sym);
    } else if (craig_var_labels[abs (literal)] == CraigVarType::B_LOCAL) {
      result.partial_interpolant_dual_sym = craig_aig_dual_sym->create_or (
          result.partial_interpolant_dual_sym,
          craig_data.partial_interpolant_dual_sym);
    } else {
      result.partial_interpolant_dual_sym = craig_aig_dual_sym->create_or (
          craig_aig_dual_sym->create_and (
              result.partial_interpolant_dual_sym,
              craig_aig_dual_sym->create_literal (-literal)),
          craig_aig_dual_sym->create_and (
              craig_data.partial_interpolant_dual_sym,
              craig_aig_dual_sym->create_literal (literal)));
    }
  }
  if (is_construction_enabled (CraigConstruction::DUAL_ASYMMETRIC)) {
    if (craig_var_labels[abs (literal)] == CraigVarType::B_LOCAL) {
      result.partial_interpolant_dual_asym =
          craig_aig_dual_asym->create_and (
              result.partial_interpolant_dual_asym,
              craig_data.partial_interpolant_dual_asym);
    } else {
      result.partial_interpolant_dual_asym =
          craig_aig_dual_asym->create_or (
              result.partial_interpolant_dual_asym,
              craig_data.partial_interpolant_dual_asym);
    }
  }
}

CraigCnfType
CraigTracer::create_craig_interpolant (CraigInterpolant interpolant,
                                       std::vector<std::vector<int>> &cnf,
                                       int &nextFreeVariable) {
  cnf.clear ();

  if (!has_craig_interpolant ()) {
    return CraigCnfType::NONE;
  }

  bool build_cnf_sym = false;
  bool build_cnf_asym = false;
  bool build_cnf_dual_sym = false;
  bool build_cnf_dual_asym = false;
  switch (interpolant) {
  case CraigInterpolant::NONE:
    break;
  case CraigInterpolant::SYMMETRIC:
    build_cnf_sym = is_construction_enabled (CraigConstruction::SYMMETRIC);
    break;
  case CraigInterpolant::ASYMMETRIC:
    build_cnf_asym =
        is_construction_enabled (CraigConstruction::ASYMMETRIC);
    break;
  case CraigInterpolant::DUAL_SYMMETRIC:
    build_cnf_dual_sym =
        is_construction_enabled (CraigConstruction::DUAL_SYMMETRIC);
    break;
  case CraigInterpolant::DUAL_ASYMMETRIC:
    build_cnf_dual_asym =
        is_construction_enabled (CraigConstruction::DUAL_ASYMMETRIC);
    break;
  case CraigInterpolant::INTERSECTION:
  case CraigInterpolant::UNION:
  case CraigInterpolant::SMALLEST:
  case CraigInterpolant::LARGEST:
    build_cnf_sym = is_construction_enabled (CraigConstruction::SYMMETRIC);
    build_cnf_asym =
        is_construction_enabled (CraigConstruction::ASYMMETRIC);
    build_cnf_dual_sym =
        is_construction_enabled (CraigConstruction::DUAL_SYMMETRIC);
    build_cnf_dual_asym =
        is_construction_enabled (CraigConstruction::DUAL_ASYMMETRIC);
    break;

  default:
    assert (false); // Seleted craig interpolation type not supported!
    __builtin_unreachable ();
  }

  std::vector<std::vector<int>> craig_cnf_sym;
  std::vector<std::vector<int>> craig_cnf_asym;
  std::vector<std::vector<int>> craig_cnf_dual_sym;
  std::vector<std::vector<int>> craig_cnf_dual_asym;
  CraigCnfType craig_cnf_type_sym = CraigCnfType::NONE;
  CraigCnfType craig_cnf_type_asym = CraigCnfType::NONE;
  CraigCnfType craig_cnf_type_dual_sym = CraigCnfType::NONE;
  CraigCnfType craig_cnf_type_dual_asym = CraigCnfType::NONE;

  if (build_cnf_sym)
    craig_cnf_type_sym = craig_aig_sym->create_cnf (
        craig_interpolant->partial_interpolant_sym, craig_cnf_sym,
        nextFreeVariable);
  if (build_cnf_asym)
    craig_cnf_type_asym = craig_aig_asym->create_cnf (
        craig_interpolant->partial_interpolant_asym, craig_cnf_asym,
        nextFreeVariable);
  if (build_cnf_dual_sym)
    craig_cnf_type_dual_sym = craig_aig_dual_sym->create_cnf (
        craig_interpolant->partial_interpolant_dual_sym, craig_cnf_dual_sym,
        nextFreeVariable);
  if (build_cnf_dual_asym)
    craig_cnf_type_dual_asym = craig_aig_dual_asym->create_cnf (
        craig_interpolant->partial_interpolant_dual_asym,
        craig_cnf_dual_asym, nextFreeVariable);

  // Dual Craig interpolants have to be inverted.
  // However, the construction rules for the dual asymmetric interpolant
  // already incorporates the negation. So only the dual symmetric
  // interpolant needs to be negated.
  if (craig_cnf_type_dual_sym == CraigCnfType::CONSTANT1) {
    craig_cnf_dual_sym = {{}};
    craig_cnf_type_dual_sym = CraigCnfType::CONSTANT0;
  } else if (craig_cnf_type_dual_sym == CraigCnfType::CONSTANT0) {
    craig_cnf_dual_sym = {};
    craig_cnf_type_dual_sym = CraigCnfType::CONSTANT1;
  } else if (craig_cnf_type_dual_sym == CraigCnfType::NORMAL) {
    craig_cnf_dual_sym.back ()[0] = -craig_cnf_dual_sym.back ()[0];
  }

  if (interpolant == CraigInterpolant::NONE) {
    cnf = {};
    return CraigCnfType::NONE;
  } else if (interpolant == CraigInterpolant::SYMMETRIC) {
    cnf = std::move (craig_cnf_sym);
    return craig_cnf_type_sym;
  } else if (interpolant == CraigInterpolant::ASYMMETRIC) {
    cnf = std::move (craig_cnf_asym);
    return craig_cnf_type_asym;
  } else if (interpolant == CraigInterpolant::DUAL_SYMMETRIC) {
    cnf = std::move (craig_cnf_dual_sym);
    return craig_cnf_type_dual_sym;
  } else if (interpolant == CraigInterpolant::DUAL_ASYMMETRIC) {
    cnf = std::move (craig_cnf_dual_asym);
    return craig_cnf_type_dual_asym;
  }

  std::vector<std::tuple<std::vector<std::vector<int>> *, CraigCnfType>>
      craig_cnfs{};
  if (craig_cnf_type_sym != CraigCnfType::NONE)
    craig_cnfs.push_back ({&craig_cnf_sym, craig_cnf_type_sym});
  if (craig_cnf_type_asym != CraigCnfType::NONE)
    craig_cnfs.push_back ({&craig_cnf_asym, craig_cnf_type_asym});
  if (craig_cnf_type_dual_sym != CraigCnfType::NONE)
    craig_cnfs.push_back ({&craig_cnf_dual_sym, craig_cnf_type_dual_sym});
  if (craig_cnf_type_dual_asym != CraigCnfType::NONE)
    craig_cnfs.push_back ({&craig_cnf_dual_asym, craig_cnf_type_dual_asym});

  if (craig_cnfs.size () == 0) {
    return CraigCnfType::NONE;
  } else if (craig_cnfs.size () == 1) {
    cnf = std::move (*std::get<0> (craig_cnfs[0]));
    return std::get<1> (craig_cnfs[0]);
  }

  // We have at least two Craig interpolants for the following computations.
  if (interpolant == CraigInterpolant::UNION) {
    bool allConstantOne = true;
    for (auto &it : craig_cnfs) {
      if (std::get<1> (it) == CraigCnfType::CONSTANT0) {
        cnf = std::move (*std::get<0> (it));
        return CraigCnfType::CONSTANT0;
      }
      allConstantOne &= (std::get<1> (it) == CraigCnfType::CONSTANT1);
    }
    if (allConstantOne) {
      cnf = {};
      return CraigCnfType::CONSTANT1;
    }

    // Create trigger (t) that enforces all CNF parts.
    int craig_trigger = nextFreeVariable++;
    std::vector<int> craig_trigger_clause{craig_trigger};
    for (auto &it : craig_cnfs) {
      if (std::get<1> (it) == CraigCnfType::NORMAL) {
        size_t i = 0, j = cnf.size ();
        cnf.resize (cnf.size () + std::get<0> (it)->size ());
        for (; i < std::get<0> (it)->size () - 1u; i++, j++)
          cnf[j] = std::move ((*std::get<0> (it))[i]);
        // The positive trigger implies that all CNF parts are enabled: (t
        // -> t_1) = (-t v t_1)
        cnf[j] = {-craig_trigger, (*std::get<0> (it))[i][0]};
        // The negative trigger implies that at least one of the CNF parts
        // is not enabled: (-t -> (-t_1 v ... v -t_n)) = (t v -t_1 v ...
        // -t_n)
        craig_trigger_clause.push_back (-(*std::get<0> (it))[i][0]);
      }
    }

    cnf.push_back (craig_trigger_clause);
    cnf.push_back ({craig_trigger});

    return CraigCnfType::NORMAL;
  } else if (interpolant == CraigInterpolant::INTERSECTION) {
    bool allConstantZero = true;
    for (auto &it : craig_cnfs) {
      if (std::get<1> (it) == CraigCnfType::CONSTANT1) {
        cnf = std::move (*std::get<0> (it));
        return CraigCnfType::CONSTANT1;
      }
      allConstantZero &= (std::get<1> (it) == CraigCnfType::CONSTANT0);
    }
    if (allConstantZero) {
      cnf = {{}};
      return CraigCnfType::CONSTANT0;
    }

    // Create trigger (t) that enforces all CNF parts.
    int craig_trigger = nextFreeVariable++;
    std::vector<int> craig_trigger_clause{-craig_trigger};
    for (auto &it : craig_cnfs) {
      if (std::get<1> (it) == CraigCnfType::NORMAL) {
        size_t i = 0, j = cnf.size ();
        cnf.resize (cnf.size () + std::get<0> (it)->size ());
        for (; i < std::get<0> (it)->size () - 1u; i++, j++)
          cnf[j] = std::move ((*std::get<0> (it))[i]);
        // The positive trigger implies that one of the CNF parts is
        // enabled: (t -> (t_1 v ... v t_n)) = (-t v t_1 v ... t_n)
        craig_trigger_clause.push_back ((*std::get<0> (it))[i][0]);
        // The negative trigger implies that at all CNF parts are not
        // enabled: (-t -> -t_1) = (t v -t_1)
        cnf[j] = {craig_trigger, -(*std::get<0> (it))[i][0]};
      }
    }

    cnf.push_back (craig_trigger_clause);
    cnf.push_back ({craig_trigger});

    return CraigCnfType::NORMAL;
  } else if (interpolant == CraigInterpolant::SMALLEST) {
    auto compare = [] (const std::tuple<std::vector<std::vector<int>> *,
                                        CraigCnfType> &elem1,
                       const std::tuple<std::vector<std::vector<int>> *,
                                        CraigCnfType> &elem2) {
      return (std::get<0> (elem1)->size () < std::get<0> (elem2)->size ());
    };
    auto minimum =
        std::min_element (craig_cnfs.begin (), craig_cnfs.end (), compare);
    cnf = std::move (*std::get<0> (*minimum));
    return std::get<1> (*minimum);
  } else if (interpolant == CraigInterpolant::LARGEST) {
    auto compare = [] (const std::tuple<std::vector<std::vector<int>> *,
                                        CraigCnfType> &elem1,
                       const std::tuple<std::vector<std::vector<int>> *,
                                        CraigCnfType> &elem2) {
      return (std::get<0> (elem1)->size () < std::get<0> (elem2)->size ());
    };
    auto maximum =
        std::max_element (craig_cnfs.begin (), craig_cnfs.end (), compare);
    cnf = std::move (*std::get<0> (*maximum));
    return std::get<1> (*maximum);
  } else {
    assert (false); // Seleted craig interpolation type not supported!
    __builtin_unreachable ();
  }
}

bool CraigTracer::is_construction_enabled (CraigConstruction construction) {
  return static_cast<uint8_t> (construction) &
         static_cast<uint8_t> (craig_construction);
}

uint8_t CraigTracer::mark_literal (int literal) {
  int index = std::abs (literal);
  uint8_t mask = (literal < 0) ? 2 : 1;

  uint8_t was_marked = marked_lits[index];
  if (!was_marked)
    marked_history.push_back (index);
  if (!(was_marked & mask))
    marked_lits[index] |= mask;
  return was_marked & ~mask;
}

void CraigTracer::unmark_all () {
  for (auto &index : marked_history) {
    marked_lits[index] = 0;
  }
  marked_history.clear ();
}

} // namespace CaDiCraig
