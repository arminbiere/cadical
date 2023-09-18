#ifndef _drattracer_h_INCLUDED
#define _drattracer_h_INCLUDED

#include "tracer.hpp"

namespace CaDiCaL {

class DratTracer : public FileTracer {

  Internal *internal;
  File *file;
  bool binary;

  int64_t added, deleted;

  void put_binary_zero ();
  void put_binary_lit (int external_lit);
  void put_binary_id (uint64_t id);

  // support DRAT
  void drat_add_clause (const vector<int> &);
  void drat_delete_clause (const vector<int> &);


public:
  // own and delete 'file'
  DratTracer (Internal *, File *file, bool binary);
  ~DratTracer ();

  void begin_proof (uint64_t) {} // skip

  void add_original_clause (uint64_t, bool, const vector<int> &) {} // skip

  void add_derived_clause (uint64_t, bool, const vector<int> &, const vector<uint64_t> &);
  
  void delete_clause (uint64_t, bool, const vector<int> &);
  
  void finalize_clause (uint64_t, const vector<int> &) {} // skip
  
  void finalize_proof (uint64_t) {} // skip

  bool closed ();
  void close ();
  void flush ();
};

} // namespace CaDiCaL

#endif
