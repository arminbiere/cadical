#ifndef _options_hpp_INCLUDED
#define _options_hpp_INCLUDED

/*------------------------------------------------------------------------*/

// The 'check' option has by default '0' in optimized compilation, but for
// debugging and testing we want to set it to '1', by default.  Setting
// 'check' to '1' for instance triggers saving all the original clauses for
// checking witnesses and also learned clauses if a solution is provided.

#ifndef NDEBUG
#define DEBUG 1
#else
#define DEBUG 0
#endif

/*------------------------------------------------------------------------*/

// Some of the 'OPTION' macros below should only be included if certain
// compile time options are enabled.  This has the effect, that for instance
// if 'LOGGING' is defined, and thus logging code is included, then also the
// 'log' option is defined.  Otherwise the 'log' option is not included.

#ifdef LOGGING
#define LOGOPT OPTION
#else
#define LOGOPT(ARGS...) /**/
#endif

#ifdef QUIET
#define QUTOPT(ARGS...) /**/
#else
#define QUTOPT OPTION
#endif

/*------------------------------------------------------------------------*/

// In order to add new option, simply add a new line below.

#define OPTIONS \
\
/*     NAME             TYPE, VAL, LO, HI, USAGE */ \
\
OPTION(arena,            int,    3, 0,  3, "1=clause,2=var,3=queue") \
OPTION(arenacompact,    bool,    1, 0,  1, "keep clauses compact") \
OPTION(arenasort,        int,    1, 0,  1, "sort clauses after arenaing") \
OPTION(binary,          bool,    1, 0,  1, "use binary proof format") \
OPTION(check,           bool,DEBUG, 0,  1, "save & check original CNF") \
OPTION(clim,             int,   -1, 0,1e9, "conflict limit (-1=none)") \
OPTION(compact,         bool,    1, 0,  1, "enable compactification") \
OPTION(compactint,       int,  1e3, 1,1e9, "compactification conflic tlimit") \
OPTION(compactlim,    double,  0.1, 0,  1, "inactive variable limit") \
OPTION(compactmin,       int,  100, 1,1e9, "inactive variable limit") \
OPTION(dlim,             int,   -1, 0,1e9, "decision limit (-1=none)") \
OPTION(elim,            bool,    1, 0,  1, "bounded variable elimination") \
OPTION(elimclslim,       int,  1e3, 0,1e9, "ignore clauses of this size") \
OPTION(eliminit,         int,  1e3, 0,1e9, "initial conflict limit") \
OPTION(elimint,          int,  1e4, 1,1e9, "initial conflict interval") \
OPTION(elimocclim,       int,  100, 0,1e9, "one sided occurrence limit") \
OPTION(elimroundsinit,   int,    5, 1,1e9, "initial number of rounds") \
OPTION(elimrounds,       int,    2, 1,1e9, "usual number of rounds") \
OPTION(emagluefast,   double, 3e-2, 0,  1, "alpha fast glue") \
OPTION(emaglueslow,   double, 1e-5, 0,  1, "alpha slow glue") \
OPTION(emajump,       double, 1e-5, 0,  1, "alpha jump level") \
OPTION(emasize,       double, 1e-5, 0,  1, "alpha learned clause size") \
OPTION(decompose,       bool,    1, 0,  1, "SCC decompose BIG and ELS") \
OPTION(decomposerounds,  int,    1, 1,1e9, "number of decompose rounds") \
OPTION(force,           bool,    0, 0,  1, "force to read broken header") \
OPTION(hbr,             bool,    1, 0,  1, "learn hyper binary clauses") \
OPTION(hbrsizelim,       int, 1e9, 3, 1e9, "max size HBR base clause") \
OPTION(keepglue,         int,    3, 1,1e9, "glue kept learned clauses") \
OPTION(keepsize,         int,    3, 2,1e9, "size kept learned clauses") \
OPTION(leak,            bool,    1, 0,  1, "leak solver memory") \
LOGOPT(log,             bool,    0, 0,  1, "enable logging") \
LOGOPT(logsort,         bool,    0, 0,  1, "sort logged clauses") \
OPTION(minimize,        bool,    1, 0,  1, "minimize learned clauses") \
OPTION(minimizedepth,    int,  1e3, 0,1e9, "minimization depth") \
OPTION(phase,            int,    1, 0,  1, "initial phase: 0=neg,1=pos") \
OPTION(posize,           int,    4, 4,1e9, "size for saving position") \
OPTION(prefetch,        bool,    1, 0,  1, "prefetch watches") \
OPTION(probe,           bool,    1, 0,  1, "failed literal probing" ) \
OPTION(probeinit,        int,  500, 0,1e9, "initial probing interval" ) \
OPTION(probeint,         int,  1e4, 1,1e9, "probing interval increment" ) \
OPTION(probereleff,   double, 0.02, 0,  1, "relative probing efficiency") \
OPTION(probemaxeff,   double,  1e7, 0,  1, "maximum probing efficiency") \
OPTION(probemineff,   double,  1e5, 0,  1, "minimum probing efficiency") \
OPTION(profile,          int,    2, 0,  4, "profiling level") \
QUTOPT(quiet,           bool,    0, 0,  1, "disable all messages") \
OPTION(reduceinc,        int,  300, 1,1e6, "reduce limit increment") \
OPTION(reduceinit,       int, 2000, 0,1e6, "initial reduce limit") \
OPTION(rephase,         bool,    1, 0,  1, "enable rephasing") \
OPTION(rephaseint,       int,  1e5, 1,1e9, "rephasing interval") \
OPTION(restart,         bool,    1, 0,  1, "enable restarting") \
OPTION(restartint,       int,    6, 1,1e9, "restart base interval") \
OPTION(restartmargin, double,  1.1, 0, 10, "restart slow fast margin") \
OPTION(reusetrail,      bool,    1, 0,  1, "enable trail reuse") \
OPTION(simplify,        bool,    1, 0,  1, "enable simplifier") \
OPTION(strengthen,      bool,    1, 0,  1, "strengthen during subsume") \
OPTION(subsume,         bool,    1, 0,  1, "enable clause subsumption") \
OPTION(subsumebinlim,    int,  1e4, 0,1e9, "watch list length limit") \
OPTION(subsumeclslim,    int,  1e3, 0,1e9, "clause length limit") \
OPTION(subsumeinc,       int,  1e4, 1,1e9, "interval in conflicts") \
OPTION(subsumeinit,      int,  1e4, 0,1e9, "initial subsume limit") \
OPTION(subsumeocclim,    int,  100, 0,1e9, "watch list length limit") \
OPTION(transred,        bool,    1, 0,  1, "transitive reduction of BIG") \
OPTION(transredreleff,double, 0.10, 0,  1, "relative efficiency") \
OPTION(transredmaxeff,double,  1e7, 0,  1, "maximum efficiency") \
OPTION(transredmineff,double,  1e5, 0,  1, "minimum efficiency") \
QUTOPT(verbose,         int,     0, 0,  2, "more verbose messages") \
OPTION(vivify,          bool,    1, 0,  1, "vivification") \
OPTION(vivifyreleff,  double, 0.03, 0,  1, "relative efficiency") \
OPTION(vivifymaxeff,  double,  1e7, 0,  1, "maximum efficiency") \
OPTION(vivifymineff,  double,  1e5, 0,  1, "minimum efficiency") \
OPTION(witness,         bool,    1, 0,  1, "print witness") \

/*------------------------------------------------------------------------*/

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
  // during accessing options at run-time and disregards the intended types,
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
  // options using 'atof'.  If the string is not a valid 'int' for 'int'
  // options or a 'double' value for 'double' options, then the function
  // returns 'false'.
  //
  bool set (const char * arg);

  // Interface to options using in a certain sense non-type-safe 'double'
  // values even for 'int' and 'bool'.  However, 'double' can hold a 'bool'
  // as well an 'int' value precisely, e.g., if the result of 'get' is cast
  // down again by the client.  This would only fail for 64 byte 'long',
  // which we currently do not support as option type.
  //
  bool has (const char * name);
  double get (const char * name);
  bool set (const char * name, double);

  void print ();             // print current values in command line form
  static void usage ();      // print usage message for all options
};

};

#endif
