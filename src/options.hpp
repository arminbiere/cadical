#ifndef _options_hpp_INCLUDED
#define _options_hpp_INCLUDED

#define OPTIONS \
/*  NAME,                TYPE, VAL,LOW,HIGH,DESCRIPTION */ \
OPTION(emagluefast,    double,4e-2, 0,  1, "alpha fast learned glue") \
OPTION(emaf1,          double,1e-3, 0,  1, "alpha learned unit frequency") \
OPTION(emaf1lim,       double,   1, 0,100, "alpha unit frequency limit") \
OPTION(ematrail,       double,1e-5, 0,  1, "alpha trail") \
OPTION(keepglue,          int,   2, 1,1e9, "glue kept learned clauses") \
OPTION(keepsize,          int,   3, 2,1e9, "size kept learned clauses") \
OPTION(minimize,         bool,   1, 0,  1, "minimize learned clauses") \
OPTION(minimizedepth,     int,1000, 0,1e9, "recursive minimization depth") \
OPTION(profile,           int,   0, 0,  4, "profiling level") \
OPTION(quiet,            bool,   0, 0,  1, "disable all messages") \
OPTION(reduce,           bool,   1, 0,  1, "garbage collect clauses") \
OPTION(reduceinc,         int, 300, 1,1e9, "reduce limit increment") \
OPTION(reduceinit,        int,2000, 0,1e9, "initial reduce limit") \
OPTION(restart,          bool,   1, 0,  1, "enable restarting") \
OPTION(restartblock,   double, 1.4, 0, 10, "restart blocking factor (R)") \
OPTION(restartblocking,  bool,   1, 0,  1, "enable restart blocking") \
OPTION(restartblocklimit, int, 1e4, 0,1e9, "restart blocking limit") \
OPTION(restartblockmargin,double,1.2,0,10, "restart blocking margin") \
OPTION(restartemaf1,     bool,   1, 0,  1, "unit frequency based restart") \
OPTION(restartint,        int,  10, 1,1e9, "restart base interval") \
OPTION(restartmargin,  double, 1.1, 0, 10, "restart slow fast margin (1/K)") \
OPTION(reusetrail,       bool,   1, 0,  1, "enable trail reuse") \
OPTION(verbose,          bool,   0, 0,  1, "more verbose messages") \
OPTION(witness,          bool,   1, 0,  1, "print witness") \

namespace CaDiCaL {

class Solver;

class Options {
  Solver * solver;
  bool set (bool &, const char *, const char *, const bool, const bool);
  bool set (int &, const char *, const char *, const int, const int);
  bool set (double &, const char *, const char *, const double, const double);
  const char * match (const char *, const char *);
public:
#define OPTION(N,T,V,L,H,D) \
  T N;
  OPTIONS
#undef OPTION
  Options (Solver *);
  bool set (const char *);	// of the form "--<opt>=<val>"
  void print ();
  static void usage ();
};

};

#endif
