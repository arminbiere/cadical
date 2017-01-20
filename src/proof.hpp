#ifndef _proof_h_INCLUDED
#define _proof_h_INCLUDED

namespace CaDiCaL {

// Provides proof tracing in the DRAT format.

class File;
class Clause;
class Internal;

class Proof {

  Internal * internal;

  File * file;
  bool binary;
  bool owned;

  void put_binary_zero ();
  void put_binary_lit (int lit);

  void trace_clause (Clause *, bool add);

  int externalize (int lit);

public:

  Proof (Internal *, File *, bool b, bool o);
  ~Proof ();

  void trace_empty_clause ();
  void trace_unit_clause (int unit);
  void trace_add_clause ();
  void trace_add_clause (Clause *);
  void trace_delete_clause (Clause *);
  void trace_flushing_clause (Clause *);
  void trace_strengthen_clause (Clause *, int);
};

};

#endif
