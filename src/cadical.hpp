#ifndef _cadical_hpp_INCLUDED
#define _cadical_hpp_INCLUDED

#include <cstdio>

namespace CaDiCaL {

// This is a wrapper or 'external' API for the CaDiCaL library.

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

  void dimacs (FILE * file);		// read DIMACS file
  void dimacs (const char * path);	// read DIMACS file

  void proof (FILE * file);		// write DRAT proof file
  void proof (const char * path);	// write DRAT proof file

private:
  
  friend class App;

  // Read solution in competition format for debugging and testing.
  //
  void solution (const char * path);    
};

};

#endif
