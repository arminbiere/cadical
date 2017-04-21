#ifndef _cadical_hpp_INCLUDED
#define _cadical_hpp_INCLUDED

#include <cstdio>
#include <vector>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// External API of the CaDiCaL solver.  In essence 'Solver' is a 'facade'
// object for 'Internal'.  It thus exposes the meant to be public API of
// 'Internal' but hides everything else (except for the private member
// functions below).  It makes it easier to understand and use the solver.

// We further map external literals to internal literals, which is
// particularly useful with many inactive variables, but also necessary, if
// we want to include approaches based on extended resolution (such as
// bounded variable addition).  The data structure necessary to maintain
// this mapping is stored in the (here opaque) 'External' data structure.

// It has the additional benefit to decouple this header file from all the
// internal data structures, which is particularly useful if the rest of the
// source is not available. For instance if only a CaDiCaL library is
// installed in a system, then only this header file has to be installed
// too, to compile and link against the library.

/*------------------------------------------------------------------------*/

class File;
class Internal;
class External;

/*------------------------------------------------------------------------*/

class Solver {

  Internal * internal;
  External * external;

public:

  Solver ();
  ~Solver ();

  void init (int new_max);      // explicitly set new maximum variable index
  int max () const;             // return maximum variable index

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

  void add (int lit);   // add literal, zero to terminate clause
  int val (int lit);    // get value (-1=false,1=true) of literal
  int solve ();         // returns 10 = SAT, 20 = UNSAT

  //------------------------------------------------------------------------

  const char * version ();	// return version string

  void banner ();       // print solver banner
  void usage ();        // print usage information for long options
  void options ();      // print current option and value list
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

  //------------------------------------------------------------------------
  // Used in the stand alone solver application 'App' which in turn uses
  // 'Signal' for catching signals and printing statistics before aborting.
  // So only these two classes need access to the otherwise more application
  // specific functions listed here.

  friend class App;
  friend class Signal;

  // Read solution in competition format for debugging and testing.
  //
  const char * solution (const char * path);

  // Messages in a common style.
  //
  void section (const char *);          // standardized section header
  void message (const char *, ...);     // verbose (level 0) message
  void error (const char *, ...);       // produce error message

  const char * dimacs (File *); // helper function factoring out common code
  File * output ();             // get access to internal 'output' file
};

};

#endif
