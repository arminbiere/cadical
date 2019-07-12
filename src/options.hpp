#ifndef _options_hpp_INCLUDED
#define _options_hpp_INCLUDED

/*------------------------------------------------------------------------*/

// In order to add a new option, simply add a new line below. Make sure that
// options are sorted correctly (with '!}sort -k 2' in 'vi').  Otherwise
// initializing the options will trigger an internal error.  For the model
// based tester 'mobical' the policy is that options which become redundant
// because another one is disabled (set to zero) should have the name of the
// latter as prefix.  In addition, one explicitly has to tell 'mobical' if
// an option becomes disabled if 'simplify' is set to zero.  The 'O' column
// determines the options which are target to 'optimize' them ('-O[1-3]').

#define OPTIONS \
\
/*      NAME         DEFAULT, LO, HI, O, USAGE */ \
\
OPTION( arena,             1,  0,  1, 0, "allocate clauses in arena") \
OPTION( arenacompact,      1,  0,  1, 0, "keep clauses compact") \
OPTION( arenasort,         1,  0,  1, 0, "sort clauses in arena") \
OPTION( arenatype,         3,  1,  3, 0, "1=clause, 2=var, 3=queue") \
OPTION( binary,            1,  0,  1, 0, "use binary proof format") \
OPTION( block,             0,  0,  1, 0, "blocked clause elimination") \
OPTION( blockmaxclslim,  1e3,  1,1e9, 1, "maximum clause size") \
OPTION( blockminclslim,    2,  2,1e9, 0, "minimum clause size") \
OPTION( blockocclim,     1e2,  1,1e9, 1, "occurrence limit") \
OPTION( bump,              1,  0,  1, 0, "bump variables") \
OPTION( bumpreason,        1,  0,  1, 0, "bump reason literals too") \
OPTION( bumpreasondepth,   1,  1,  3, 0, "bump reason depth") \
OPTION( check,             0,  0,  1, 0, "enable internal checking") \
OPTION( checkassumptions,  1,  0,  1, 0, "check assumptions satisfied") \
OPTION( checkfailed,       1,  0,  1, 0, "check failed literals form core") \
OPTION( checkfrozen,       0,  0,  1, 0, "check all frozen semantics") \
OPTION( checkproof,        1,  0,  1, 0, "check proof internally") \
OPTION( checkwitness,      1,  0,  1, 0, "check witness internally") \
OPTION( chrono,            1,  0,  2, 0, "chronological backtracking") \
OPTION( chronoalways,      0,  0,  1, 0, "force always chronological") \
OPTION( chronolevelim,   1e2,  0,1e9, 0, "chronological level limit") \
OPTION( chronoreusetrail,  1,  0,  1, 0, "reuse trail chronologically") \
OPTION( compact,           1,  0,  1, 0, "compact internal variables") \
OPTION( compactint,      2e3,  1,1e9, 0, "compacting interval") \
OPTION( compactlim,      1e2,  0,1e3, 0, "inactive limit in per mille") \
OPTION( compactmin,      1e2,  1,1e9, 0, "minimum inactive limit") \
OPTION( cover,             0,  0,  1, 0, "covered clause elimination") \
OPTION( covermaxeff,     1e8,  0,1e9, 1, "maximum cover efficiency") \
OPTION( covermineff,     1e6,  0,1e9, 1, "minimum cover efficiency") \
OPTION( coverreleff,       4,  0,1e3, 1, "relative efficiency per mille") \
OPTION( decompose,         1,  0,  1, 0, "decompose BIG in SCCs and ELS") \
OPTION( decomposerounds,   2,  1, 16, 0, "number of decompose rounds") \
OPTION( deduplicate,       1,  0,  1, 0, "remove duplicated binary clauses") \
OPTION( eagersubsume,      1,  0,  1, 0, "subsume eagerly recently learned") \
OPTION( eagersubsumelim,  20,  1,1e3, 0, "limit on subsumed candidates") \
OPTION( elim,              1,  0,  1, 0, "bounded variable elimination") \
OPTION( elimands,          1,  0,  1, 0, "find AND gates") \
OPTION( elimaxeff,       1e9,  0,1e9, 1, "maximum elimination efficiency") \
OPTION( elimbackward,      1,  0,  1, 0, "eager backward subsumption") \
OPTION( elimboundmax,     16, -1,256, 1, "maximum elimination bound") \
OPTION( elimboundmin,      0, -1,1e3, 0, "minimum elimination bound") \
OPTION( elimclslim,      1e2,  2,1e9, 1, "resolvent size limit") \
OPTION( elimequivs,        1,  0,  1, 0, "find equivalence gates") \
OPTION( elimineff,       1e7,  0,1e9, 1, "minimum elimination efficiency") \
OPTION( elimint,         2e3,  1,1e9, 0, "elimination interval") \
OPTION( elimites,          1,  0,  1, 0, "find if-then-else gates") \
OPTION( elimlimited,       1,  0,  1, 0, "limit resolutions") \
OPTION( elimocclim,      1e3,  0,1e9, 1, "occurrence limit") \
OPTION( elimprod,          1,  0,1e4, 0, "elimination score product") \
OPTION( elimreleff,      1e3,  0,1e4, 1, "relative efficiency per mille") \
OPTION( elimrounds,        2,  1,512, 0, "usual number of rounds") \
OPTION( elimsubst,         1,  0,  1, 0, "elimination by substitution") \
OPTION( elimxorlim,        5,  2, 27, 1, "maximum XOR size") \
OPTION( elimxors,          1,  0,  1, 0, "find XOR gates") \
OPTION( emagluefast,      33,  1,1e9, 0, "window fast glue") \
OPTION( emaglueslow,     1e5,  1,1e9, 0, "window slow glue") \
OPTION( emajump,         1e5,  1,1e9, 0, "window back-jump level") \
OPTION( emalevel,        1e5,  1,1e9, 0, "window back-track level") \
OPTION( emasize,         1e5,  1,1e9, 0, "window learned clause size") \
OPTION( ematrailfast,    1e2,  1,1e9, 0, "window fast trail") \
OPTION( ematrailslow,    1e5,  1,1e9, 0, "window slow trail") \
OPTION( flush,             1,  0,  1, 0, "flush redundant clauses") \
OPTION( flushfactor,       3,  1,1e3, 0, "interval increase") \
OPTION( flushint,        1e5,  1,1e9, 0, "initial limit") \
OPTION( forcephase,        0,  0,  1, 0, "always use initial phase") \
OPTION( inprocessing,      1,  0,  1, 0, "enable inprocessing") \
OPTION( instantiate,       0,  0,  1, 0, "variable instantiation") \
OPTION( instantiateclslim, 3,  2,1e9, 0, "minimum clause size") \
OPTION( instantiateocclim, 1,  1,1e9, 1, "maximum occurrence limit") \
OPTION( instantiateonce,   1,  0,  1, 0, "instantiate each clause once") \
LOGOPT( log,               0,  0,  1, 0, "enable logging") \
LOGOPT( logsort,           0,  0,  1, 0, "sort logged clauses") \
OPTION( lucky,             1,  0,  1, 0, "search for lucky phases") \
OPTION( minimize,          1,  0,  1, 0, "minimize learned clauses") \
OPTION( minimizedepth,   1e3,  0,1e3, 0, "minimization depth") \
OPTION( phase,             1,  0,  1, 0, "initial phase") \
OPTION( probe,             1,  0,  1, 0, "failed literal probing" ) \
OPTION( probehbr,          1,  0,  1, 0, "learn hyper binary clauses") \
OPTION( probeint,        5e3,  1,1e9, 0, "probing interval" ) \
OPTION( probemaxeff,     1e8,  0,1e9, 1, "maximum probing efficiency") \
OPTION( probemineff,     1e6,  0,1e9, 1, "minimum probing efficiency") \
OPTION( probereleff,      20,  0,1e3, 1, "relative efficiency per mille") \
OPTION( proberounds,       1,  1, 16, 0, "probing rounds" ) \
OPTION( profile,           2,  0,  4, 0, "profiling level") \
QUTOPT( quiet,             0,  0,  1, 0, "disable all messages") \
OPTION( radixsortlim,    800,  0,1e9, 0, "radix sort limit") \
OPTION( realtime,          0,  0,  1, 0, "real instead of process time") \
OPTION( reduce,            1,  0,  1, 0, "reduce useless clauses") \
OPTION( reduceint,       300, 10,1e6, 0, "reduce interval") \
OPTION( reducekeepglue,    3,  1,1e9, 0, "glue of kept learned clauses") \
OPTION( reducetarget,     75, 10,1e2, 0, "reduce fraction in percent") \
OPTION( reluctant,      1024,  0,1e9, 0, "reluctant doubling period") \
OPTION( reluctantmax,1048576,  0,1e9, 0, "reluctant doubling period") \
OPTION( rephase,           1,  0,  1, 0, "enable resetting phase") \
OPTION( rephaseint,      1e3,  1,1e9, 0, "rephase interval") \
OPTION( report,report_default_value,  0,  1, 0, "enable reporting") \
OPTION( reportall,         0,  0,  1, 0, "report even if not successful") \
OPTION( reportsolve,       0,  0,  1, 0, "use solving not process time") \
OPTION( restart,           1,  0,  1, 0, "enable restarts") \
OPTION( restartint,        2,  1,1e9, 0, "restart interval") \
OPTION( restartmargin,    10,  0,1e2, 0, "slow fast margin in percent") \
OPTION( restartreusetrail, 1,  0,  1, 0, "enable trail reuse") \
OPTION( restoreall,        0,  0,  2, 0, "restore all clauses (2=really)") \
OPTION( restoreflush,      0,  0,  1, 0, "remove satisfied clauses") \
OPTION( reverse,           0,  0,  1, 0, "reverse variable ordering") \
OPTION( score,             1,  0,  1, 0, "use EVSIDS scores") \
OPTION( scorefactor,     950,500,1e3, 0, "score factor per mille") \
OPTION( seed,              0,  0,1e9, 0, "random seed") \
OPTION( shuffle,           0,  0,  1, 0, "shuffle variables") \
OPTION( shufflequeue,      1,  0,  1, 0, "shuffle variable queue") \
OPTION( shufflerandom,     0,  0,  1, 0, "not reverse but random") \
OPTION( shufflescores,     1,  0,  1, 0, "shuffle variable scores") \
OPTION( simplify,          1,  0,  1, 0, "enable simplifier") \
OPTION( stabilize,         1,  0,  1, 0, "enable stabilizing phases") \
OPTION( stabilizefactor, 200,101,1e9, 0, "phase increase in percent") \
OPTION( stabilizeint,    1e3,  1,1e9, 0, "stabilizing interval") \
OPTION( stabilizemaxint, 1e9,  1,1e9, 0, "maximum stabilizing phase") \
OPTION( stabilizeonly,     0,  0,  1, 0, "only stabilizing phases") \
OPTION( stabilizephase,    1,  0,  1, 0, "use target variable phase") \
OPTION( subsume,           1,  0,  1, 0, "enable clause subsumption") \
OPTION( subsumebinlim,   1e4,  0,1e9, 1, "watch list length limit") \
OPTION( subsumeclslim,   1e3,  0,1e9, 1, "clause length limit") \
OPTION( subsumeint,      1e4,  1,1e9, 0, "subsume interval") \
OPTION( subsumelimited,    1,  0,  1, 0, "limit subsumption checks") \
OPTION( subsumemaxeff,   1e8,  0,1e9, 1, "maximum subsuming efficiency") \
OPTION( subsumemineff,   1e6,  0,1e9, 1, "minimum subsuming efficiency") \
OPTION( subsumeocclim,   1e2,  0,1e9, 1, "watch list length limit") \
OPTION( subsumereleff,   1e3,  0,1e4, 1, "relative efficiency per mille") \
OPTION( subsumestr,        1,  0,  1, 0, "strengthen during subsume") \
OPTION( ternary,           1,  0,  1, 0, "hyper ternary resolution") \
OPTION( ternarymaxadd,   1e3,  0,1e4, 0, "maximum clauses added in percent") \
OPTION( ternarymaxeff,   1e8,  0,1e9, 1, "ternary maximum efficiency") \
OPTION( ternarymineff,   1e6,  1,1e9, 1, "minimum ternary efficiency") \
OPTION( ternaryocclim,   1e2,  1,1e9, 1, "ternary occurrence limit") \
OPTION( ternaryreleff,    10,  0,1e5, 1, "relative efficiency in per mille") \
OPTION( ternaryrounds,     2,  1, 16, 0, "maximum ternary rounds") \
OPTION( transred,          1,  0,  1, 0, "transitive reduction of BIG") \
OPTION( transredmaxeff,  1e8,  0,1e9, 1, "maximum efficiency") \
OPTION( transredmineff,  1e6,  0,1e9, 1, "minimum efficiency") \
OPTION( transredreleff,  1e2,  0,1e3, 1, "relative efficiency per mille") \
QUTOPT( verbose,           0,  0,  3, 0, "more verbose messages") \
OPTION( vivify,            1,  0,  1, 0, "vivification") \
OPTION( vivifymaxeff,    1e8,  0,1e9, 1, "maximum efficiency") \
OPTION( vivifymineff,    1e5,  0,1e9, 1, "minimum efficiency") \
OPTION( vivifyonce,        0,  0,  2, 0, "vivify once: 1=red, 2=red+irr") \
OPTION( vivifyredeff,    300,  0,1e3, 1, "redundant efficiency per mille") \
OPTION( vivifyreleff,     80,  0,1e3, 1, "relative efficiency per mille") \
OPTION( walk,              1,  0,  1, 0, "enable random walks") \
OPTION( walkmaxeff,      1e7,  0,1e9, 0, "maximum efficiency") \
OPTION( walkmineff,      1e5,  0,1e7, 0, "minimum efficiency") \
OPTION( walknonstable,     1,  0,  1, 0, "walk in non-stabilizing phase") \
OPTION( walkredundant,     0,  0,  1, 0, "walk redundant clauses too") \
OPTION( walkreleff,       20,  0,1e3, 1, "relative efficiency per mille") \

// Note, keep an empty line right before this line because of the last '\'!
// Also keep those single spaces after 'OPTION(' for proper sorting.

/*------------------------------------------------------------------------*/

// Some of the 'OPTION' macros above should only be included if certain
// compile time options are enabled.  This has the effect, that for instance
// if 'LOGGING' is defined, and thus logging code is included, then also the
// 'log' option is defined.  Otherwise the 'log' option is not included.

#ifdef LOGGING
#define LOGOPT OPTION
#else
#define LOGOPT(...) /**/
#endif

#ifdef QUIET
#define QUTOPT(...) /**/
#else
#define QUTOPT OPTION
#endif

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

struct Internal;

/*------------------------------------------------------------------------*/

class Options;

struct Option {
  const char * name;
  int def, lo, hi, optimizable;
  const char * description;
  int & val (Options *);
};

/*------------------------------------------------------------------------*/

// Produce a compile time constant for the number of options.

static const size_t number_of_options =
#define OPTION(N,V,L,H,O,D) 1 +
OPTIONS
#undef OPTION
+ 0;

/*------------------------------------------------------------------------*/

class Options {

  Internal * internal;

  void set (Option *, int val); // Force to [lo,hi] interval.

  friend struct Option;
  static Option table[];

  static void initialize_from_environment (
    int & val, const char * name, const int L, const int H);

public:
  
  // For library usage we disable reporting by default while for the stand
  // alone SAT solver we enable it by default.  This default value has to
  // be set before the constructor of 'Options' is called.
  //
  static int report_default_value;

  Options (Internal *);

  // Makes options directly accessible, e.g., for instance declares the
  // member 'int restart' here.  This will give fast access to option values
  // internally in the solver and thus can also be used in tight loops.
  //
  int __start_of_options__;             // Used by 'val' below.
# define OPTION(N,V,L,H,O,D) \
  int N;                                // Access option values by name.
  OPTIONS
# undef OPTION

  // It would be more elegant to use an anonymous 'struct' of the actual
  // option values overlayed with an 'int values[number_of_options]' array
  // but that is not proper ISO C++ and produces a warning.  Instead we use
  // the following construction which relies on '__start_of_options__'.
  //
  inline int & val (size_t idx) {
    assert (idx < number_of_options);
    return (&__start_of_options__ + 1)[idx];
  }

  // With the following function we can get rather fast access to the option
  // limits, the default value and the description.  The code uses binary
  // search over the sorted option 'table'.  This static data is shared
  // among different instances of the solver.  The actual current option
  // values are here in the 'Options' class.  They can be accessed by the
  // offset of the static options through the 'vals' field using
  // 'Option::val' if you have an 'Option' or to have even faster access
  // directly by the member function (the 'N' above, e.g., 'restart').
  //
  static Option * has (const char * name);

  bool set (const char * name, int);    // Explicit version.
  int  get (const char * name);         // Get current value.

  void config (const char * name);      // Configuration.

  void print ();             // Print current values in command line form
  static void usage ();      // Print usage message for all options.

  void optimize (int val);   // increase some limits (val=0,1,2,3)

  // Parse option value string in the form of
  //
  //   true
  //   false
  //   [-]<mantissa>[e<exponent>]
  //
  // and in the latter case '<val>' has to be within [-INT_MAX,INT_MAX].
  // The function returns true if parsing is successful and then also sets
  // the second argument to the parsed value.
  //
  static bool parse_option_value (const char *, int &);

  // Parse long option argument
  //
  //   --<name>
  //   --<name>=<val>
  //   --no-<name>
  //
  // where '<val>' is as in 'parse_option_value'.  If parsing succeeds,
  // 'true' is returned and the string will be set to the name of the
  // option.  Additionally the parsed value is set (last argument).
  //
  static bool parse_long_option (const char *, string &, int &);

  // Iterating options.

  typedef Option * iterator;
  typedef const Option * const_iterator;

  static iterator begin () { return table; }
  static iterator end () { return table + number_of_options; }
};

inline int & Option::val (Options * opts) {
  assert (Options::table <= this && this < Options::table + number_of_options);
  return opts->val (this - Options::table);
}

}

#endif
