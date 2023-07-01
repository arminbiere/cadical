#ifndef _proof_h_INCLUDED
#define _proof_h_INCLUDED

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

class File;
struct Clause;
struct Internal;
class Checker;
class Tracer;
class LratBuilder;
class LratChecker;

/*------------------------------------------------------------------------*/

// Provides proof checking and writing.

class Proof {

  Internal *internal;

  vector<int> clause;           // of external literals
  vector<uint64_t> proof_chain; // lrat style proof chain of clause
  uint64_t clause_id;           // id of added clause

  // the 'observers'
  Checker *checker;         // drat checker with unit propagation
  Tracer *tracer;           // trace proof to file
  LratBuilder *lratbuilder; // create lrat proof chain for any clause
  LratChecker *lratchecker; // lrat checker

  void add_literal (int internal_lit); // add to 'clause'
  void add_literals (Clause *);        // add to 'clause'

  void add_literals (const vector<int> &); // ditto

  void add_original_clause (); // notify observers of original clauses
  void add_derived_clause ();  // notify observers of derived clauses
  void delete_clause ();       // notify observers of deleted clauses
  void finalize_clause ();

public:
  Proof (Internal *);
  ~Proof ();

  void connect (Tracer *t) { tracer = t; }
  void connect (LratBuilder *lb) { lratbuilder = lb; }
  void connect (LratChecker *lc) { lratchecker = lc; }
  void connect (Checker *c) { checker = c; }

  // Add original clauses to the proof (for online proof checking).
  //
  void add_original_clause (uint64_t, const vector<int> &);

  // Add/delete original clauses to/from the proof using their original
  //  external literals (from external->eclause)
  // TODO: add ids...
  //
  void add_external_original_clause (uint64_t, const vector<int> &);
  void delete_external_original_clause (uint64_t, const vector<int> &);

  // Add derived (such as learned) clauses to the proof.
  //
  void add_derived_empty_clause (uint64_t);
  void add_derived_unit_clause (uint64_t, int unit);
  void add_derived_clause (Clause *);
  void add_derived_clause (uint64_t, const vector<int> &);

  void add_derived_empty_clause (uint64_t, const vector<uint64_t> &);
  void add_derived_unit_clause (uint64_t, int unit,
                                const vector<uint64_t> &);
  void add_derived_clause (Clause *c, const vector<uint64_t> &);
  void add_derived_clause (uint64_t, const vector<int> &,
                           const vector<uint64_t> &);

  void delete_clause (uint64_t, const vector<int> &);
  void delete_unit_clause (uint64_t id, const int lit);
  void delete_clause (Clause *);

  void finalize_unit (uint64_t, int);
  void finalize_clause (uint64_t, const vector<int> &c);
  void finalize_clause (Clause *);

  // These two actually pretend to add and remove a clause.
  //
  void flush_clause (Clause *);           // remove falsified literals
  void strengthen_clause (Clause *, int); // remove second argument
  void strengthen_clause (Clause *, int, const vector<uint64_t> &);
  void otfs_strengthen_clause (Clause *, const vector<int> &,
                               const vector<uint64_t> &);
  void otfs_strengthen_clause (Clause *, const vector<int> &);

  void flush ();
};

} // namespace CaDiCaL

#endif
