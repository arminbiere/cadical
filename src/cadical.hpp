#ifndef _cadical_hpp_INCLUDED
#define _cadical_hpp_INCLUDED

#include <cstdio>

namespace CaDiCaL {

// External API of the CaDiCaL solver.

class Internal;

class Solver {

  Internal * internal;

public:

  Solver ();
  ~Solver ();

  //------------------------------------------------------------------------
  // Option handling.

  bool set (const char * name, const int val);
  bool set (const char * name, const bool val);
  bool set (const char * name, const double val);

  bool get (const char * name, int & val);
  bool get (const char * name, bool & val);
  bool get (const char * name, double & val);

  //------------------------------------------------------------------------
  // Core functionality as in the IPASIR incremental SAT solver interface.

  void add (int lit);	// add literal, zero to terminate clause
  int val (int lit);	// get value (-1=false,1=true) of literal
  int solve ();		// returns 10 = SAT, 20 = UNSAT

  //------------------------------------------------------------------------

  void banner ();	// print solver banner
  void options ();	// print current option and value list
  void witness ();	// print witness in competition format
  void statistics ();   // print statistics

  //------------------------------------------------------------------------
  // Files with explicit path argument support compressed input and output
  // if appropriate helper functions 'gzip' etc. are available.  They are
  // called through opening a pipe to an external command.

  // Returns zero if successful and otherwise an error message.
  //
  const char * dimacs (FILE * file);	    // read DIMACS file
  const char * dimacs (const char * path);  // read DIMACS file

  // Enables clausal proof tracing in DRAT format and returns 'true' if
  // successfully opened for writing.  Writing proofs has to be enabled
  // before calling 'solve', 'add' and 'dimacs'.  Otherwise only partial
  // proofs are written.
  //
  bool proof (FILE * file);	   // write DRAT proof file
  bool proof (const char * path);  // write DRAT proof file
  void close ();                   // close proof file

private:
  
  friend class App;

  // Read solution in competition format for debugging and testing.
  //
  const char * solution (const char * path);    
};

};

#endif
