#ifndef _options_hpp_INCLUDED
#define _options_hpp_INCLUDED

/*------------------------------------------------------------------------*/

// In order to add a new option, simply add a new line below. Make sure that
// options are sorted correctly (with '!}sort -k 2' in 'vi').  Otherwise
// initializing the options will trigger an internal error.  For the model
// based tester 'mobical' the policy is that options which become redundant
// because another one is disabled (set to zero) should have the name of the
// latter as prefix.  The 'O' column determines the options which are
// target to 'optimize' them ('-O[1-3]').  A zero value in the 'O' column
// means that this option is not optimized.  A value of '1' results in
// optimizing its value exponentially with exponent base '2', and a value
// of '2' uses base '10'.  The 'P' column determines simplification
// options (disabled with '--plain') and 'R' which values can be reset.

#define OPTIONS \
\
/*      NAME         DEFAULT, LO, HI,O,P,R, USAGE */ \
\
OPTION( arena,             1,  0,  1,0,0,1, "allocate clauses in arena") \
OPTION( arenacompact,      1,  0,  1,0,0,1, "keep clauses compact") \
OPTION( arenasort,         1,  0,  1,0,0,1, "sort clauses in arena") \
OPTION( arenatype,         3,  1,  3,0,0,1, "1=clause, 2=var, 3=queue") \
OPTION( binary,            1,  0,  1,0,0,1, "use binary proof format") \
OPTION( block,             0,  0,  1,0,1,1, "blocked clause elimination") \
OPTION( blockmaxclslim,  1e5,  1,2e9,2,0,1, "maximum clause size") \
OPTION( blockminclslim,    2,  2,2e9,0,0,1, "minimum clause size") \
OPTION( blockocclim,     1e2,  1,2e9,2,0,1, "occurrence limit") \
OPTION( bump,              1,  0,  1,0,0,1, "bump variables") \
OPTION( bumpreason,        1,  0,  1,0,0,1, "bump reason literals too") \
OPTION( bumpreasondepth,   1,  1,  3,0,0,1, "bump reason depth") \
OPTION( check,             0,  0,  1,0,0,0, "enable internal checking") \
OPTION( checkassumptions,  1,  0,  1,0,0,0, "check assumptions satisfied") \
OPTION( checkconstraint,   1,  0,  1,0,0,0, "check constraint satisfied") \
OPTION( checkfailed,       1,  0,  1,0,0,0, "check failed literals form core") \
OPTION( checkfrozen,       0,  0,  1,0,0,0, "check all frozen semantics") \
OPTION( checkproof,        1,  0,  1,0,0,0, "check proof internally") \
OPTION( checkwitness,      1,  0,  1,0,0,0, "check witness internally") \
OPTION( chrono,            1,  0,  2,0,0,1, "chronological backtracking") \
OPTION( chronoalways,      0,  0,  1,0,0,1, "force always chronological") \
OPTION( chronolevelim,   1e2,  0,2e9,0,0,1, "chronological level limit") \
OPTION( chronoreusetrail,  1,  0,  1,0,0,1, "reuse trail chronologically") \
OPTION( compact,           1,  0,  1,0,1,1, "compact internal variables") \
OPTION( compactint,      2e3,  1,2e9,0,0,1, "compacting interval") \
OPTION( compactlim,      1e2,  0,1e3,0,0,1, "inactive limit per mille") \
OPTION( compactmin,      1e2,  1,2e9,0,0,1, "minimum inactive limit") \
OPTION( condition,         0,  0,  1,0,0,1, "globally blocked clause elim") \
OPTION( conditionint,    1e4,  1,2e9,0,0,1, "initial conflict interval") \
OPTION( conditionmaxeff, 1e7,  0,2e9,1,0,1, "maximum condition efficiency") \
OPTION( conditionmaxrat, 100,  1,2e9,1,0,1, "maximum clause variable ratio") \
OPTION( conditionmineff, 1e6,  0,2e9,1,0,1, "minimum condition efficiency") \
OPTION( conditionreleff, 100,  1,1e5,0,0,1, "relative efficiency per mille") \
OPTION( cover,             0,  0,  1,0,1,1, "covered clause elimination") \
OPTION( covermaxclslim,  1e5,  1,2e9,2,0,1, "maximum clause size") \
OPTION( covermaxeff,     1e8,  0,2e9,1,0,1, "maximum cover efficiency") \
OPTION( coverminclslim,    2,  2,2e9,0,0,1, "minimum clause size") \
OPTION( covermineff,     1e6,  0,2e9,1,0,1, "minimum cover efficiency") \
OPTION( coverreleff,       4,  1,1e5,1,0,1, "relative efficiency per mille") \
OPTION( decompose,         1,  0,  1,0,1,1, "decompose BIG in SCCs and ELS") \
OPTION( decomposerounds,   2,  1, 16,1,0,1, "number of decompose rounds") \
OPTION( deduplicate,       1,  0,  1,0,1,1, "remove duplicated binaries") \
OPTION( eagersubsume,      1,  0,  1,0,0,1, "subsume recently learned") \
OPTION( eagersubsumelim,  20,  1,1e3,0,0,1, "limit on subsumed candidates") \
OPTION( elim,              1,  0,  1,0,1,1, "bounded variable elimination") \
OPTION( elimands,          1,  0,  1,0,0,1, "find AND gates") \
OPTION( elimaxeff,       2e9,  0,2e9,1,0,1, "maximum elimination efficiency") \
OPTION( elimbackward,      1,  0,  1,0,0,1, "eager backward subsumption") \
OPTION( elimboundmax,     16, -1,2e6,1,0,1, "maximum elimination bound") \
OPTION( elimboundmin,      0, -1,2e6,0,0,1, "minimum elimination bound") \
OPTION( elimclslim,      1e2,  2,2e9,2,0,1, "resolvent size limit") \
OPTION( elimequivs,        1,  0,  1,0,0,1, "find equivalence gates") \
OPTION( elimineff,       1e7,  0,2e9,1,0,1, "minimum elimination efficiency") \
OPTION( elimint,         2e3,  1,2e9,0,0,1, "elimination interval") \
OPTION( elimites,          1,  0,  1,0,0,1, "find if-then-else gates") \
OPTION( elimlimited,       1,  0,  1,0,0,1, "limit resolutions") \
OPTION( elimocclim,      1e2,  0,2e9,2,0,1, "occurrence limit") \
OPTION( elimprod,          1,  0,1e4,0,0,1, "elim score product weight") \
OPTION( elimreleff,      1e3,  1,1e5,1,0,1, "relative efficiency per mille") \
OPTION( elimrounds,        2,  1,512,1,0,1, "usual number of rounds") \
OPTION( elimsubst,         1,  0,  1,0,0,1, "elimination by substitution") \
OPTION( elimsum,           1,  0,1e4,0,0,1, "elimination score sum weight") \
OPTION( elimxorlim,        5,  2, 27,1,0,1, "maximum XOR size") \
OPTION( elimxors,          1,  0,  1,0,0,1, "find XOR gates") \
OPTION( emagluefast,      33,  1,2e9,0,0,1, "window fast glue") \
OPTION( emaglueslow,     1e5,  1,2e9,0,0,1, "window slow glue") \
OPTION( emajump,         1e5,  1,2e9,0,0,1, "window back-jump level") \
OPTION( emalevel,        1e5,  1,2e9,0,0,1, "window back-track level") \
OPTION( emasize,         1e5,  1,2e9,0,0,1, "window learned clause size") \
OPTION( ematrailfast,    1e2,  1,2e9,0,0,1, "window fast trail") \
OPTION( ematrailslow,    1e5,  1,2e9,0,0,1, "window slow trail") \
OPTION( flush,             0,  0,  1,0,0,1, "flush redundant clauses") \
OPTION( flushfactor,       3,  1,1e3,0,0,1, "interval increase") \
OPTION( flushint,        1e5,  1,2e9,0,0,1, "initial limit") \
OPTION( forcephase,        0,  0,  1,0,0,1, "always use initial phase") \
OPTION( inprocessing,      1,  0,  1,0,0,1, "enable inprocessing") \
OPTION( instantiate,       0,  0,  1,0,1,1, "variable instantiation") \
OPTION( instantiateclslim, 3,  2,2e9,0,0,1, "minimum clause size") \
OPTION( instantiateocclim, 1,  1,2e9,2,0,1, "maximum occurrence limit") \
OPTION( instantiateonce,   1,  0,  1,0,0,1, "instantiate each clause once") \
LOGOPT( log,               0,  0,  1,0,0,0, "enable logging") \
LOGOPT( logsort,           0,  0,  1,0,0,0, "sort logged clauses") \
OPTION( lucky,             1,  0,  1,0,0,1, "search for lucky phases") \
OPTION( minimize,          1,  0,  1,0,0,1, "minimize learned clauses") \
OPTION( minimizedepth,   1e3,  0,1e3,0,0,1, "minimization depth") \
OPTION( phase,             1,  0,  1,0,0,1, "initial phase") \
OPTION( probe,             1,  0,  1,0,1,1, "failed literal probing" ) \
OPTION( probehbr,          1,  0,  1,0,0,1, "learn hyper binary clauses") \
OPTION( probeint,        5e3,  1,2e9,0,0,1, "probing interval" ) \
OPTION( probemaxeff,     1e8,  0,2e9,1,0,1, "maximum probing efficiency") \
OPTION( probemineff,     1e6,  0,2e9,1,0,1, "minimum probing efficiency") \
OPTION( probereleff,      20,  1,1e5,1,0,1, "relative efficiency per mille") \
OPTION( proberounds,       1,  1, 16,1,0,1, "probing rounds" ) \
OPTION( profile,           2,  0,  4,0,0,0, "profiling level") \
QUTOPT( quiet,             0,  0,  1,0,0,0, "disable all messages") \
OPTION( radixsortlim,    800,  0,2e9,0,0,1, "radix sort limit") \
OPTION( realtime,          0,  0,  1,0,0,0, "real instead of process time") \
OPTION( reduce,            1,  0,  1,0,0,1, "reduce useless clauses") \
OPTION( reduceint,       300, 10,1e6,0,0,1, "reduce interval") \
OPTION( reducetarget,     75, 10,1e2,0,0,1, "reduce fraction in percent") \
OPTION( reducetier1glue,   2,  1,2e9,0,0,1, "glue of kept learned clauses") \
OPTION( reducetier2glue,   6,  1,2e9,0,0,1, "glue of tier two clauses") \
OPTION( reluctant,      1024,  0,2e9,0,0,1, "reluctant doubling period") \
OPTION( reluctantmax,1048576,  0,2e9,0,0,1, "reluctant doubling period") \
OPTION( rephase,           1,  0,  1,0,0,1, "enable resetting phase") \
OPTION( rephaseint,      1e3,  1,2e9,0,0,1, "rephase interval") \
OPTION( report,reportdefault,  0,  1,0,0,1, "enable reporting") \
OPTION( reportall,         0,  0,  1,0,0,1, "report even if not successful") \
OPTION( reportsolve,       0,  0,  1,0,0,1, "use solving not process time") \
OPTION( restart,           1,  0,  1,0,0,1, "enable restarts") \
OPTION( restartint,        2,  1,2e9,0,0,1, "restart interval") \
OPTION( restartmargin,    10,  0,1e2,0,0,1, "slow fast margin in percent") \
OPTION( restartreusetrail, 1,  0,  1,0,0,1, "enable trail reuse") \
OPTION( restoreall,        0,  0,  2,0,0,1, "restore all clauses (2=really)") \
OPTION( restoreflush,      0,  0,  1,0,0,1, "remove satisfied clauses") \
OPTION( reverse,           0,  0,  1,0,0,1, "reverse variable ordering") \
OPTION( score,             1,  0,  1,0,0,1, "use EVSIDS scores") \
OPTION( scorefactor,     950,500,1e3,0,0,1, "score factor per mille") \
OPTION( seed,              0,  0,2e9,0,0,1, "random seed") \
OPTION( shrink,            3,  0,  3,0,0,1, "shrink conflict clause") \
OPTION( shrinkreap,        1,  0,  1,0,0,1, "use a reap for shrinking") \
OPTION( shuffle,           0,  0,  1,0,0,1, "shuffle variables") \
OPTION( shufflequeue,      1,  0,  1,0,0,1, "shuffle variable queue") \
OPTION( shufflerandom,     0,  0,  1,0,0,1, "not reverse but random") \
OPTION( shufflescores,     1,  0,  1,0,0,1, "shuffle variable scores") \
OPTION( stabilize,         1,  0,  1,0,0,1, "enable stabilizing phases") \
OPTION( stabilizefactor, 200,101,2e9,0,0,1, "phase increase in percent") \
OPTION( stabilizeint,    1e3,  1,2e9,0,0,1, "stabilizing interval") \
OPTION( stabilizemaxint, 2e9,  1,2e9,0,0,1, "maximum stabilizing phase") \
OPTION( stabilizeonly,     0,  0,  1,0,0,1, "only stabilizing phases") \
OPTION( subsume,           1,  0,  1,0,1,1, "enable clause subsumption") \
OPTION( subsumebinlim,   1e4,  0,2e9,1,0,1, "watch list length limit") \
OPTION( subsumeclslim,   1e2,  0,2e9,2,0,1, "clause length limit") \
OPTION( subsumeint,      1e4,  1,2e9,0,0,1, "subsume interval") \
OPTION( subsumelimited,    1,  0,  1,0,0,1, "limit subsumption checks") \
OPTION( subsumemaxeff,   1e8,  0,2e9,1,0,1, "maximum subsuming efficiency") \
OPTION( subsumemineff,   1e6,  0,2e9,1,0,1, "minimum subsuming efficiency") \
OPTION( subsumeocclim,   1e2,  0,2e9,1,0,1, "watch list length limit") \
OPTION( subsumereleff,   1e3,  1,1e5,1,0,1, "relative efficiency per mille") \
OPTION( subsumestr,        1,  0,  1,0,0,1, "strengthen during subsume") \
OPTION( target,            1,  0,  2,0,0,1, "target phases (1=stable only)") \
OPTION( terminateint,     10,  0,1e4,0,0,1, "termination check interval") \
OPTION( ternary,           1,  0,  1,0,1,1, "hyper ternary resolution") \
OPTION( ternarymaxadd,   1e3,  0,1e4,1,0,1, "max clauses added in percent") \
OPTION( ternarymaxeff,   1e8,  0,2e9,1,0,1, "ternary maximum efficiency") \
OPTION( ternarymineff,   1e6,  1,2e9,1,0,1, "minimum ternary efficiency") \
OPTION( ternaryocclim,   1e2,  1,2e9,2,0,1, "ternary occurrence limit") \
OPTION( ternaryreleff,    10,  1,1e5,1,0,1, "relative efficiency per mille") \
OPTION( ternaryrounds,     2,  1, 16,1,0,1, "maximum ternary rounds") \
OPTION( transred,          1,  0,  1,0,1,1, "transitive reduction of BIG") \
OPTION( transredmaxeff,  1e8,  0,2e9,1,0,1, "maximum efficiency") \
OPTION( transredmineff,  1e6,  0,2e9,1,0,1, "minimum efficiency") \
OPTION( transredreleff,  1e2,  1,1e5,1,0,1, "relative efficiency per mille") \
QUTOPT( verbose,           0,  0,  3,0,0,0, "more verbose messages") \
OPTION( vivify,            1,  0,  1,0,1,1, "vivification") \
OPTION( vivifymaxeff,    2e7,  0,2e9,1,0,1, "maximum efficiency") \
OPTION( vivifymineff,    2e4,  0,2e9,1,0,1, "minimum efficiency") \
OPTION( vivifyonce,        0,  0,  2,0,0,1, "vivify once: 1=red, 2=red+irr") \
OPTION( vivifyredeff,     75,  0,1e3,1,0,1, "redundant efficiency per mille") \
OPTION( vivifyreleff,     20,  1,1e5,1,0,1, "relative efficiency per mille") \
OPTION( walk,              1,  0,  1,0,0,1, "enable random walks") \
OPTION( walkmaxeff,      1e7,  0,2e9,1,0,1, "maximum efficiency") \
OPTION( walkmineff,      1e5,  0,1e7,1,0,1, "minimum efficiency") \
OPTION( walknonstable,     1,  0,  1,0,0,1, "walk in non-stabilizing phase") \
OPTION( walkredundant,     0,  0,  1,0,0,1, "walk redundant clauses too") \
OPTION( walkreleff,       20,  1,1e5,1,0,1, "relative efficiency per mille") \

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
  int def, lo, hi;
  int optimizable;
  bool preprocessing;
  const char * description;
  int & val (Options *);
};

/*------------------------------------------------------------------------*/

// Produce a compile time constant for the number of options.

static const size_t number_of_options =
#define OPTION(N,V,L,H,O,P,R,D) 1 +
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

  friend Config;

  void reset_default_values ();
  void disable_preprocessing ();

public:

  // For library usage we disable reporting by default while for the stand
  // alone SAT solver we enable it by default.  This default value has to
  // be set before the constructor of 'Options' is called (which in turn is
  // called from the constructor of 'Solver').  If we would simply overwrite
  // its initial value while initializing the stand alone solver,  we will
  // get that change of the default value (from 'false' to 'true') shown
  // during calls to 'print ()', which is confusing to the user.
  //
  static int reportdefault;

  Options (Internal *);

  // Makes options directly accessible, e.g., for instance declares the
  // member 'int restart' here.  This will give fast access to option values
  // internally in the solver and thus can also be used in tight loops.
  //
private:
  int __start_of_options__;             // Used by 'val' below.
public:
# define OPTION(N,V,L,H,O,P,R,D) \
  int N;                                // Access option values by name.
  OPTIONS
# undef OPTION

  // It would be more elegant to use an anonymous 'struct' of the actual
  // option values overlayed with an 'int values[number_of_options]' array
  // but that is not proper ISO C++ and produces a warning.  Instead we use
  // the following construction which relies on '__start_of_options__' and
  // that the following options are really allocated directly after it.
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
  // offset of the static options using 'Option::val' if you have an
  // 'Option' or to have even faster access directly by the member function
  // (the 'N' above, e.g., 'restart').
  //
  static Option * has (const char * name);

  bool set (const char * name, int);    // Explicit version.
  int  get (const char * name);         // Get current value.

  void print ();             // Print current values in command line form
  static void usage ();      // Print usage message for all options.

  void optimize (int val);   // increase some limits (val=0..31)

  static bool is_preprocessing_option (const char * name);

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

  void copy (Options & other) const;    // Copy 'this' into 'other'.
};

inline int & Option::val (Options * opts) {
  assert (Options::table <= this && this < Options::table + number_of_options);
  return opts->val (this - Options::table);
}

}

#endif
