#ifndef _iruptracer_h_INCLUDED
#define _iruptracer_h_INCLUDED

class FileTracer;

namespace CaDiCaL {

struct IrupClause {
  IrupClause *next;  // collision chain link for hash table
  uint64_t hash; // previously computed full 64-bit hash
  uint64_t id;   // id of clause
  unsigned size;  
  int literals[1];
};

class IrupTracer : public FileTracer {

  Internal *internal;
  File *file;
  bool binary;
  
  // hash table for conclusion
  //
  uint64_t num_clauses;  // number of clauses in hash table
  uint64_t size_clauses; // size of clause hash table
  IrupClause **clauses;      // hash table of clauses
  vector<int> imported_clause;
  
  static const unsigned num_nonces = 4;

  uint64_t nonces[num_nonces]; // random numbers for hashing
  uint64_t last_hash;          // last computed hash value of clause
  uint64_t last_id;            // id of the last added clause
  IrupClause *last_clause;
  uint64_t compute_hash (uint64_t); // compute and save hash value of clause

  IrupClause *new_clause ();
  void delete_clause (IrupClause *);

  static uint64_t reduce_hash (uint64_t hash, uint64_t size);

  void enlarge_clauses (); // enlarge hash table for clauses
  void insert ();          // insert clause in hash table
  bool find_and_delete (const uint64_t); // find clause position in hash table


  int64_t added, deleted;

  void put_binary_zero ();
  void put_binary_lit (int external_lit);
  void put_binary_id (uint64_t id);

  void irup_add_derived_clause (const vector<int> &clause);
  void irup_delete_clause (uint64_t id, const vector<int> &clause);
  void irup_add_restored_clause (const vector<int> &clause);
  void irup_conclude_and_delete (const vector<uint64_t> &conclusion);

public:

  IrupTracer (Internal *, File *file, bool);
  ~IrupTracer ();
  
  // proof section: 
  void add_derived_clause (uint64_t, bool, const vector<int> &,
                           const vector<uint64_t> &) override;
  void add_assumption_clause (uint64_t, const vector<int> &,
                                      const vector<uint64_t> &) override;
  void weaken_minus (uint64_t, const vector<int> &) override;
  void delete_clause (uint64_t, bool, const vector<int> &) override;
  void conclude_proof (ConclusionType, const vector<uint64_t> &) override;
  void add_original_clause (uint64_t, bool, const vector<int> &,
                                    bool = false) override;

  // skip
  void begin_proof (uint64_t) override {}
  void finalize_clause (uint64_t, const vector<int> &) override {}
  void finalize_proof (uint64_t) override {}
  void strengthen (uint64_t) override {}
  void add_assumption (int) override {}
  void add_constraint (const vector<int> &) override {}
  void reset_assumptions () override {}


  // logging and file io
  void connect_internal (Internal *i) override;

  bool closed () override;
  void close () override;
  void flush () override;
};

} // namespace CaDiCaL

#endif
