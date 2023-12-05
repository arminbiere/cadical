#ifndef _frattracer_h_INCLUDED
#define _frattracer_h_INCLUDED

namespace CaDiCaL {

class FratTracer : public FileTracer {

  Internal *internal;
  File *file;
  bool binary;
  bool with_antecedents;

#ifndef QUIET
  int64_t added, deleted;
  int64_t finalized, original;
#endif

  vector<uint64_t> delete_ids;

  void put_binary_zero ();
  void put_binary_lit (int external_lit);
  void put_binary_id (uint64_t id);

  // support FRAT
  void frat_add_original_clause (uint64_t, const vector<int> &);
  void frat_add_derived_clause (uint64_t, const vector<int> &);
  void frat_add_derived_clause (uint64_t, const vector<int> &,
                                const vector<uint64_t> &);
  void frat_delete_clause (uint64_t, const vector<int> &);
  void frat_finalize_clause (uint64_t, const vector<int> &);

public:
  // own and delete 'file'
  FratTracer (Internal *, File *file, bool binary, bool antecedents);
  ~FratTracer ();

  void connect_internal (Internal *i) override;
  void begin_proof (uint64_t) override {} // skip

  void add_original_clause (uint64_t, bool, const vector<int> &,
                            bool = false) override;

  void add_derived_clause (uint64_t, bool, const vector<int> &,
                           const vector<uint64_t> &) override;

  void delete_clause (uint64_t, bool, const vector<int> &) override;

  void finalize_clause (uint64_t, const vector<int> &) override;

  void report_status (int, uint64_t) override {} // skip

#ifndef QUIET
  void print_statistics ();
#endif
  bool closed () override;
  void close (bool) override;
  void flush (bool) override;
};

} // namespace CaDiCaL

#endif
