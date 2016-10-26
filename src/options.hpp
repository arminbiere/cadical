#ifndef _options_hpp_INCLUDED
#define _options_hpp_INCLUDED

#ifndef NDEBUG
#define DBG 1
#else
#define DBG 0
#endif

#define OPTIONS \
/*     NAME              TYPE, VAL,LO, HI, USAGE */ \
OPTION(arena,            int,   3, 0,  3, "1=clause,2=var,3=queue") \
OPTION(binary,          bool,   1, 0,  1, "use binary proof format") \
OPTION(check,           bool, DBG, 0,  1, "save & check original CNF") \
OPTION(emagluefast,   double,3e-2, 0,  1, "alpha fast learned glue") \
OPTION(emaglueslow,   double,1e-5, 0,  1, "alpha fast learned glue") \
OPTION(keepglue,         int,   2, 1,1e9, "glue kept learned clauses") \
OPTION(keepsize,         int,   3, 2,1e9, "size kept learned clauses") \
OPTION(leak,            bool,   1, 0,  1, "leak solver memory") \
OPTION(minimize,        bool,   1, 0,  1, "minimize learned clauses") \
OPTION(minimizedepth,    int,1000, 0,1e9, "minimization depth") \
OPTION(prefetch,        bool,   1, 0,  1, "prefetch watches") \
OPTION(profile,          int,   1, 0,  4, "profiling level") \
OPTION(quiet,           bool,   0, 0,  1, "disable all messages") \
OPTION(reduce,          bool,   1, 0,  1, "garbage collect clauses") \
OPTION(reduceglue,      bool,   1, 0,  1, "reduce on glue first") \
OPTION(reduceinc,        int, 300, 1,1e9, "reduce limit increment") \
OPTION(reduceinit,       int,2000, 0,1e9, "initial reduce limit") \
OPTION(resolve,         bool,   1, 0,  1, "bump resolved clauses") \
OPTION(restart,         bool,   1, 0,  1, "enable restarting") \
OPTION(restartint,       int,  10, 1,1e9, "restart base interval") \
OPTION(restartmargin, double, 1.1, 0, 10, "restart slow fast margin") \
OPTION(reusetrail,      bool,   1, 0,  1, "enable trail reuse") \
OPTION(strengthen,      bool,   1, 0,  1, "strengthen during subsume") \
OPTION(sublast,          int,   5, 0,1e4, "eagerly subsume last") \
OPTION(subsume,         bool,   1, 0,  1, "enable clause subsumption") \
OPTION(subsumeffort,  double,  10, 1,1e9, "checked clauses wrt interval") \
OPTION(subsumeinc,       int, 1e4, 1,1e9, "interval in conflicts") \
OPTION(subsumeinit,      int, 1e4, 0,1e9, "intial subsume limit") \
OPTION(subsumelim,       int,  20, 0,1e9, "watch list length limit") \
OPTION(verbose,         bool,   0, 0,  1, "more verbose messages") \
OPTION(witness,         bool,   1, 0,  1, "print witness") \

namespace CaDiCaL {

class Internal;

class Options {

  Internal * internal;

  bool set (   int &, const char *, const char *, const    int, const    int);
  bool set (  bool &, const char *, const char *, const   bool, const   bool);
  bool set (double &, const char *, const char *, const double, const double);

  const char * match (const char *, const char *);

public:

  // Makes options directly accessible, e.g., for instance declares the
  // member 'bool Options.restart' here.  This will give fast and type save
  // access to option values (internally).  In principle one could make all
  // options simply 'double' though, but that requires double conversions
  // during accessing options at run-time and disregard the intended types,
  // e.g., one would need to allow fractional values for actual integer
  // or boolean options.  Keeping the different types makes the output of
  // 'print' and 'usage' also more appealing (since correctly typed values
  // are printed).

#define OPTION(N,T,V,L,H,D) \
  T N;
  OPTIONS
#undef OPTION

  Options (Internal *);

  // This sets the value of an option assuming a 'long' command line
  // argument form.  The argument 'arg' thus should look like
  //
  //  "--<NAME>=<VAL>", "--<NAME>" or "--no-<NAME>"
  //
  // where 'NAME' is one of the option names above.  Returns 'true' if the
  // option was parsed and set correctly.  For boolean values we strictly
  // only allow "true", "false", "0" and "1" as "<VAL>" string.  For 'int'
  // type options we parse "<VAL>" with 'atoi' and force the resulting 'int'
  // value to the 'LO' and 'HI' range and similarly for 'double' type
  // options using 'atof'.  Thus in both cases we do not check whether
  // "<VAL>" is actually a string representing a proper 'int' or 'double'
  // which is also quite difficult for the latter.
  //
  bool set (const char * arg);

  // Interface to options using in a certain sense non-type-safe 'double'
  // values even for 'int' and 'bool'.  However, since 'double' can hold a
  // 'bool' and ' with typing, since a 'double' can hold a 'bool' as well an
  // 'int' value precisely, e.g., if the result of 'get' cast down again by
  // the client.
  //
  bool has (const char * name);
  double get (const char * name);
  bool set (const char * name, double);

  void print ();             // print current values in command line form
  static void usage ();      // print usage message for all options
};

};

#endif
