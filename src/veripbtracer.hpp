#ifndef _veripbtracer_h_INCLUDED
#define _veripbtracer_h_INCLUDED

class FileTracer;

namespace CaDiCaL {

struct HashId {
  HashId *next;  // collision chain link for hash table
  uint64_t hash; // previously computed full 64-bit hash
  uint64_t id;   // id of clause
};

class VeripbTracer : public FileTracer {

  Internal *internal;
  File *file;
#ifndef NDEBUG
  bool binary;
#endif
  bool with_antecedents;
  bool checked_deletions;

  // hash table for checked deletions
  //
  uint64_t num_clauses;  // number of clauses in hash table
  uint64_t size_clauses; // size of clause hash table
  HashId **clauses;      // hash table of clauses

  static const unsigned num_nonces = 4;

  uint64_t nonces[num_nonces]; // random numbers for hashing
  uint64_t last_hash;          // last computed hash value of clause
  uint64_t last_id;            // id of the last added clause
  HashId *last_clause;
  uint64_t compute_hash (uint64_t); // compute and save hash value of clause

  HashId *new_clause ();
  void delete_clause (HashId *);

  // Reduce hash value to the actual size.
  //
  static uint64_t reduce_hash (uint64_t hash, uint64_t size);

  void enlarge_clauses (); // enlarge hash table for clauses
  void insert ();          // insert clause in hash table
  bool
  find_and_delete (const uint64_t); // find clause position in hash table

#ifndef QUIET
  int64_t added, deleted;
#endif
  vector<uint64_t> delete_ids;

  void put_binary_zero ();
  void put_binary_lit (int external_lit);
  void put_binary_id (uint64_t id);

  // support veriPB
  void veripb_add_derived_clause (uint64_t, bool redundant,
                                  const vector<int> &clause,
                                  const vector<uint64_t> &chain);
  void veripb_add_derived_clause (uint64_t, bool redundant,
                                  const vector<int> &clause);
  void veripb_begin_proof (uint64_t reserved_ids);
  void veripb_delete_clause (uint64_t id, bool redundant);
  void veripb_report_status (bool unsat, uint64_t conflict_id);
  void veripb_strengthen (uint64_t);

public:
  // own and delete 'file'
  VeripbTracer (Internal *, File *file, bool, bool, bool);
  ~VeripbTracer ();

  void connect_internal (Internal *i) override;
  void begin_proof (uint64_t) override;

  void add_original_clause (uint64_t, bool, const vector<int> &,
                            bool = false) override {} // skip

  void add_derived_clause (uint64_t, bool, const vector<int> &,
                           const vector<uint64_t> &) override;

  void delete_clause (uint64_t, bool, const vector<int> &) override;
  void finalize_clause (uint64_t, const vector<int> &) override {} // skip

  void report_status (int, uint64_t) override;

  void weaken_minus (uint64_t, const vector<int> &) override;
  void strengthen (uint64_t) override;

#ifndef QUIET
  void print_statistics ();
#endif
  bool closed () override;
  void close (bool) override;
  void flush (bool) override;
};

} // namespace CaDiCaL

#endif
