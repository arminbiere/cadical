#ifndef _veripbtracer_h_INCLUDED
#define _veripbtracer_h_INCLUDED

class FileTracer;

namespace CaDiCaL {

class VeripbTracer : public FileTracer {

  Internal *internal;
  File *file;
  bool binary;
  bool with_antecedents;
  bool checked_deletions;

  int64_t added, deleted;

  vector<uint64_t> delete_ids;

  void put_binary_zero ();
  void put_binary_lit (int external_lit);
  void put_binary_id (uint64_t id);

  // support veriPB
  void veripb_add_derived_clause (bool redundant, const vector<int> &clause,
                                  const vector<uint64_t> &chain);
  void veripb_add_derived_clause (bool redundant, const vector<int> &clause);
  void veripb_begin_proof (uint64_t reserved_ids);
  void veripb_delete_clause (uint64_t id, bool redundant);
  void veripb_finalize_proof (uint64_t conflict_id);


public:
  // own and delete 'file'
  VeripbTracer (Internal *, File *file, bool, bool, bool);
  ~VeripbTracer ();

  void begin_proof (uint64_t) override;

  void add_original_clause (uint64_t, bool, const vector<int> &, bool = false) override {} // skip

  void add_derived_clause (uint64_t, bool, const vector<int> &, const vector<uint64_t> &) override;
  
  void delete_clause (uint64_t, bool, const vector<int> &) override;
  void finalize_clause (uint64_t, const vector<int> &) override {} // skip
  
  void finalize_proof (uint64_t) override;

  bool closed () override;
  void close () override;
  void flush () override;
};

} // namespace CaDiCaL

#endif
