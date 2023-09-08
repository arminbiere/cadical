#ifndef _veripbtracer_h_INCLUDED
#define _veripbtracer_h_INCLUDED

class FileTracer;

namespace CaDiCaL {

class VeripbTracer : public FileTracer {

  Internal *internal;
  File *file;
  bool binary;
  bool with_antecedents;

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
  void veripb_delete_clause (bool redundant, uint64_t id);
  void veripb_finalize_proof (uint64_t conflict_id);


public:
  // own and delete 'file'
  VeripbTracer (Internal *, File *file, bool binary, bool antecedents);
  ~VeripbTracer ();

  void begin_proof (uint64_t);

  void add_original_clause (uint64_t, bool, const vector<int> &) {} // skip

  void add_derived_clause (uint64_t, bool, const vector<int> &, const vector<uint64_t> &);
  
  void delete_clause (uint64_t, bool, const vector<int> &);
  
  void finalize_clause (uint64_t, const vector<int> &) {} // skip
  
  void finalize_proof (uint64_t);

  bool closed ();
  void close ();
  void flush ();
};

} // namespace CaDiCaL

#endif
