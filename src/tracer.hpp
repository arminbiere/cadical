#ifndef _tracer_h_INCLUDED
#define _tracer_h_INCLUDED

// Proof tracing to a file (actually 'File') in DRAT/FRAT format.

namespace CaDiCaL {

class Tracer {

  Internal *internal;
  File *file;
  bool binary;
  bool lrat;
  bool frat;
  bool veripb;

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

  // support FRAT
  void frat_add_original_clause (uint64_t, const vector<int> &);
  void frat_add_derived_clause (uint64_t, const vector<int> &);
  void frat_add_derived_clause (uint64_t, const vector<int> &,
                                const vector<uint64_t> &);
  void frat_delete_clause (uint64_t, const vector<int> &);
  void frat_finalize_clause (uint64_t, const vector<int> &);

  // support veriPB
  void veripb_add_derived_clause (const vector<int> &clause,
                                  const vector<uint64_t> &chain);
  void veripb_begin_proof (uint64_t reserved_ids);
  void veripb_delete_clause (uint64_t id);

  // support DRAT
  void drat_add_clause (const vector<int> &);
  void drat_delete_clause (const vector<int> &);

public:
  // own and delete 'file'
  Tracer (Internal *, File *file, bool binary, bool lrat, bool frat,
          bool veripb);
  ~Tracer ();

  void add_derived_clause (uint64_t, const vector<int> &);
  void add_derived_clause (uint64_t, const vector<int> &,
                           const vector<uint64_t> &);
  void delete_clause (uint64_t, const vector<int> &);
  void add_original_clause (uint64_t, const vector<int> &); // for frat
  void finalize_clause (uint64_t, const vector<int> &);     // for frat
  void set_first_id (uint64_t);
  void veripb_finalize_proof (uint64_t);

  bool closed ();
  void close ();
  void flush ();
};

} // namespace CaDiCaL

#endif
