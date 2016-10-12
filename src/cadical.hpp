#ifndef _cadical_hpp_INCLUDED
#define _cadical_hpp_INCLUDED

#include <cstdio>

namespace CaDiCaL {

// External API of the CaDiCaL solver.  In essence 'Solver' is a 'facade'
// object for 'Internal'.  It thus exposes the meant to be public API of
// 'Internal' and should make it easier to understand and use the solver.
// It has the additional benefit to decouple this header file from all
// the internal data structures.

class Internal;

class Solver {

  Internal * internal;

public:

  Solver ();
  ~Solver ();

  int max () const;	// return maximum variable index

  //------------------------------------------------------------------------
  // Option handling.

  bool has (const char * name);
  double get (const char * name);
  bool set (const char * name, double val);

  // command line form: '--<name>=<val>', '--<name>', or '--no-<name>'
  //
  bool set (const char * arg);

  //------------------------------------------------------------------------
  // Core functionality as in the IPASIR incremental SAT solver interface.

  void add (int lit);	// add literal, zero to terminate clause
  int val (int lit);	// get value (-1=false,1=true) of literal
  int solve ();		// returns 10 = SAT, 20 = UNSAT

  //------------------------------------------------------------------------

  void banner ();	// print solver banner
  void options ();	// print current option and value list
  void statistics ();   // print statistics

  //------------------------------------------------------------------------
  // Files with explicit path argument support compressed input and output
  // if appropriate helper functions 'gzip' etc. are available.  They are
  // called through opening a pipe to an external command.

  // Returns zero if successful and otherwise an error message.
  //
  const char * dimacs (FILE * file, const char * name); // read DIMACS
  const char * dimacs (const char * path);              // open & read

  // Enables clausal proof tracing in DRAT format and returns 'true' if
  // successfully opened for writing.  Writing proofs has to be enabled
  // before calling 'solve', 'add' and 'dimacs'.  Otherwise only partial
  // proofs are written.
  //
  void proof (FILE * file, const char * name); // write DRAT proof file
  bool proof (const char * path);              // open & write DRAT proof
  void close ();                               // close proof (early)

private:
  
  friend class App;
  friend class Signal;

  // Read solution in competition format for debugging and testing.
  //
  const char * solution (const char * path);    

  // Messages in a common style.
  //
  void msg (const char *, ...);
  void err (const char *, ...);
  void section (const char *);
};

};

#endif
