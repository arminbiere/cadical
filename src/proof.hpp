#ifndef _proof_h_INCLUDED
#define _proof_h_INCLUDED

namespace CaDiCaL {

class File;
class Clause;
class Solver;

class Proof {
  File * file;
  bool enabled;
  void trace_clause (Clause *, bool add);
public:
  Proof () : file (0), enabled (false) { }
  Proof (File * f) :  file (f), enabled (true) { }
  operator bool () const { return enabled; }
  void trace_empty_clause ();
  void trace_unit_clause (int unit);
  void trace_add_clause (Clause *);
  void trace_delete_clause (Clause *);
  void trace_flushing_clause (Solver *, Clause *);
};

};

#endif
