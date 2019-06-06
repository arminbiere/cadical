#ifndef _tracer_h_INCLUDED
#define _tracer_h_INCLUDED

#include "observer.hpp" // Alphabetically after 'tracer'.

// Proof tracing to a file (actually 'File') in DRAT format.

namespace CaDiCaL {

class Tracer : public Observer {
  Internal * internal;
  File * file;
  bool binary;
  void put_binary_zero ();
  void put_binary_lit (int external_lit);
public:

  Tracer (Internal *, File * file, bool binary); // own and delete 'file'
  ~Tracer ();

  void add_derived_clause (const vector<int> &);
  void delete_clause (const vector<int> &);
  bool closed ();
  void close ();
};

}

#endif
