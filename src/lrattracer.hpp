#ifndef _lrattracer_h_INCLUDED
#define _lrattracer_h_INCLUDED


namespace CaDiCaL {

class LratTracer : public FileTracer {

  Internal *internal;
  File *file;
  bool binary;

  int64_t added, deleted;
  uint64_t latest_id;
  vector<uint64_t> delete_ids;

  void put_binary_zero ();
  void put_binary_lit (int external_lit);
  void put_binary_id (uint64_t id);

 // support LRAT
  void lrat_add_clause (uint64_t, const vector<int> &,
                        const vector<uint64_t> &);
  void lrat_delete_clause (uint64_t);


public:
  // own and delete 'file'
  LratTracer (Internal *, File *file, bool binary);
  ~LratTracer ();

  void begin_proof (uint64_t) override;

  void add_original_clause (uint64_t, bool, const vector<int> &, bool = false) override {} // skip

  void add_derived_clause (uint64_t, bool, const vector<int> &, const vector<uint64_t> &) override;
  
  void delete_clause (uint64_t, bool, const vector<int> &) override;
  
  void finalize_clause (uint64_t, const vector<int> &) override {} // skip
  
  void finalize_proof (uint64_t) override {} // skip

  bool closed () override;
  void close () override;
  void flush () override;
};

} // namespace CaDiCaL

#endif
