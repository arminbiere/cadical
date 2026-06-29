/*------------------------------------------------------------------------*/
/* Copyright (C) 2018-2021 Armin Biere, Johannes Kepler University Linz   */
/* Copyright (C) 2020-2021 Mathias Fleury, Johannes Kepler University Linz*/
/* Copyright (c) 2020-2021 Nils Froleyks, Johannes Kepler University Linz */
/* Copyright (C) 2022-2025 Katalin Fazekas, Technical University of Vienna*/
/* Copyright (C) 2021-2025 Armin Biere, University of Freiburg            */
/* Copyright (C) 2021-2025 Mathias Fleury, University of Freiburg         */
/* Copyright (C) 2023-2025 Florian Pollitt, University of Freiburg */
/* Copyright (C) 2024-2024 Tobias Faller, University of Freiburg   */
/*------------------------------------------------------------------------*/

// Model Based Tester for the CaDiCaL SAT Solver Library.

#include <memory>
namespace CaDiCaL {

// clang-format off

static const char *USAGE =
"usage: mobical [ <option> ... ] [ <mode> ]\n"
"\n"
"where '<option>' can be one of the following:\n"
"\n"
"  --help    | -h    print this command line option summary and exit\n"
"  --version         print CaDiCaL's three character version and exit\n"
"  --build           print build configuration\n"
"\n"
"  -v | --verbose    increase verbosity\n"
"  -q | --quiet      be quiet (only print failing and reduced traces)\n"
"\n"
"  --colors          force colors for both '<stdout>' and '<stderr>'\n"
"  --no-colors       disable colors if '<stderr>' is connected to terminal\n"
"  --no-terminal     assume '<stderr>' is not connected to terminal\n"
"  --no-seeds        do not print seeds in random mode\n"
"  --no-summary      force not to print detailed summary\n"
"  --summary         force to print detailed summary\n"
"\n"
"  -<n>              specify the number of solving phases explicitly\n"
"  --time <seconds>  set time limit per trace (none=0, default=%d)\n"
"  --space <MB>      set space limit (none=0, default=%d)\n"
"  --no-bad-alloc    switch off failing memory allocations, monitor for crashes\n"
"  --no-leak-alloc   switch off tracking of memory allocations, monitor for memory leaks\n"
"  --no-terminator   switch off generation of termination requests, monitor for crashes\n"
"\n"
"  --do-not-ignore-resource-limits consider out-of-time or memory as error\n"
"\n"
"  --tiny            generate tiny formulas only\n"
"  --small           generate small formulas only\n"
"  --medium          generate medium sized formulas only\n"
"  --big             generate big formulas only\n"
"\n"
"Then '<mode>' is one of these\n"
"\n"
"  <seed>            generate and execute trace for given 64-bit seed\n"
"  <seed>  <output>  generate trace, shrink and write it to file\n"
"  <input> <output>  read trace, shrink and write it to output file\n"
"  <input>           read and replay the specified input trace\n"
"\n"
"In order to let the test execute '<r>' runs (starting from '<seed>') use:\n"
"\n"
"  -L[ ]<r>          execute '<r>' runs\n"
"  -X[ ]<r>          execute '<r>' bugs\n"
"\n"
"Fix solver options independent of the (generated) trace content:\n"
"\n"
"  -F[ ]<option>     with '<option>' as in cadical but without '--' prefix\n"
"\n"
"The output trace is not shrunken if it is not failing.  However, before\n"
"it is written it is executed, unless '--do-not-execute' is specified:\n"
"\n"
"  --do-not-execute  just write to '<output>' without execution\n"
"\n"
"In order to check memory issues or collect coverage you can force\n"
"execution within the main process, which however also means that the\n"
"model based tester aborts as soon a test fails\n"
"\n"
"  --do-not-fork     execute all tests in main process directly\n"
"\n"
"In order to replay a trace which violates an API contract use\n"
"\n"
"  --do-not-enforce-contracts\n"
"\n"
"When replaying a trace with user propagator, use the following\n"
"  --no-mock         disable mock propagator (allows replay of propagators)\n"
"  --no-mock-relaxed does not fail if the replay diverges from the trace\n"
"\n"
"To read from '<stdin>' use '-' as '<input>' and also '-' instead of\n"
"'<output>' to write to '<stdout>'.\n"
"\n"
"As the library is compiled with logging support ('-DLOGGING')\n"
"one can force to add the 'set log 1' call to the trace with\n"
"\n"
"  --log | -l        force low-level logging for detailed debugging\n"
"\n"
"Implicitly add 'dump' and 'stats' calls to traces:\n"
"\n"
"  --dump  | -d      force dumping the CNF before every 'solve'\n"
"  --stats | -s      force printing statistics after every 'solve'\n"
"\n"
"Implicitly add 'configure plain' after setting options:\n"
"\n"
"  --plain | -p\n" // TODO all configurations?
"\n"
"Otherwise if no '<mode>' is specified the default is to generate random\n"
"traces internally until the execution of a trace fails, which means it\n"
"produces a non-zero exit code.  Then the trace is rerun and shrunken\n"
"through delta-debugging to produce a smaller trace.  The shrunken failing\n"
"trace is written as 'red-<seed>.trace' to the current working directory.\n"
"\n"
"The following options disable certain parts of the shrinking "
"algorithm:\n"
"\n"
"  --do-not-shrink[-at-all]\n"
"  --do-not-add-options[-before-shrinking]\n"
"  --do-not-shrink-phases\n"
"  --do-not-shrink-clauses\n"
"  --do-not-shrink-literals\n"
"  --do-not-shrink-basic[-calls]\n"
"  --do-not-disable[-options]\n"
"  --do-not-reduce[[-option]-values]\n"
"  --do-not-shrink-variables\n"
"  --do-not-shrink-options\n"
"  --do-not-shrink-propagator\n"
"\n"
"The standard mode of using the model based tester is to start it in\n"
"random testing mode without '<input>', '<seed>' nor '<output>' option.\n"
"If a failing trace is found it will be shrunken and the resulting\n"
"trace written to the current working directory.  Then the model based\n"
"tester can be interrupted and then called again with the produced\n"
"failing trace as single argument.\n"
"\n"
"This second invocation will execute the trace within the same process\n"
"and thus can directly be investigated with a symbolic debugger such\n"
"as 'gdb' or maybe first checked for memory issues with 'valgrind'\n"
"or recompilation with memory checking '-fsanitize=address'.\n"
;

// clang-format on

} // namespace CaDiCaL

/*------------------------------------------------------------------------*/

#include "internal.hpp"
#include "signal.hpp"

/*------------------------------------------------------------------------*/

#include <cstdarg>
#include <cstddef>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <regex>
#include <sstream>
#include <string>
#include <vector>

// MockPropagator
#include <deque>
#include <map>
#include <set>

/*------------------------------------------------------------------------*/

extern "C" {
#ifdef MOBICAL_MEMORY
#include <cxxabi.h>
#include <dlfcn.h>
#include <execinfo.h>
#endif
#ifdef MOBICAL_TERMINATE
#include <cxxabi.h>
#include <execinfo.h>
#endif
#include <unistd.h>
}

#ifdef MOBICAL_MEMORY
typedef void *(*malloc_t) (size_t);
typedef void *(*realloc_t) (void *, size_t);
typedef void (*free_t) (void *);
static malloc_t libc_malloc = nullptr;
static realloc_t libc_realloc = nullptr;
static free_t libc_free = nullptr;
static malloc_t hook_malloc = nullptr;
static realloc_t hook_realloc = nullptr;
static free_t hook_free = nullptr;

void *malloc (size_t size) {
  return hook_malloc ? (*hook_malloc) (size) : (*libc_malloc) (size);
}
void *realloc (void *ptr, size_t size) {
  return hook_realloc ? (*hook_realloc) (ptr, size)
                      : (*libc_realloc) (ptr, size);
}
void free (void *ptr) {
  (hook_free) ? (*hook_free) (ptr) : (*libc_free) (ptr);
}

void initialize_allocators () {
  libc_malloc = reinterpret_cast<malloc_t> (dlsym (RTLD_NEXT, "malloc"));
  libc_realloc = reinterpret_cast<realloc_t> (dlsym (RTLD_NEXT, "realloc"));
  libc_free = reinterpret_cast<free_t> (dlsym (RTLD_NEXT, "free"));
}
__attribute__ ((section (".preinit_array"))) void (*init_allocators_ptr) (
    void) = initialize_allocators;
#endif

/*------------------------------------------------------------------------*/
namespace CaDiCaL { // All except 'main' below.
/*------------------------------------------------------------------------*/

using namespace std;

class Reader;
class Trace;

#define DEFAULT_TIME_LIMIT 10
#define DEFAULT_SPACE_LIMIT 1024

/*------------------------------------------------------------------------*/

// Options to generate traces.

enum Size { NOSIZE = 0, TINY = 5, SMALL = 10, MEDIUM = 30, BIG = 50 };

struct Force {
  Size size = NOSIZE;
  int phases = -1;
};

// Options to shrink traces.

struct DoNot {
  bool add = false;          // add all options before shrinking    'a'
  struct {                   //
    bool atall = false;      // do not shrink anything              's'
    bool phases = false;     // shrink complete incremental solving 'p'
    bool clauses = false;    // shrink full clauses                 'c'
    bool lemmas = false;     // shrink external lemmas              'u'
    bool literals = false;   // shrink literals which shrinks       'l'
    bool basic = false;      // shrink other basic calls            'b'
    bool options = false;    // shrink option calls                 'o'
    bool propagator = false; // shrink propagator calls             'e'
  } shrink;                  //
  bool disable = false;      // try to eagerly disable all options  'd'
  bool map = false;          // do not map variable indices         'm'
  bool reduce = false;       // reduce option values                'r'
  bool execute = false;      // do not execute trace
  bool fork = false;         // do not fork sub-process
  bool enforce = false;      // do not enforce contracts on read trace
  bool seeds = false;
  bool summary = false;
  bool ignore_resource_limits = false;
  bool mock_propagator = false;
  bool replay_strict = false;
};

/*------------------------------------------------------------------------*/

class Mopts;

struct Mopt {
  const char *name;
  int value;
  bool fixed;
  int &val (Mopts *);
  bool &fix (Mopts *);
  Mopt (const char *n) : name (n), value (0), fixed (0) {};
};

class Mopts {

  void set (Mopt *o, int val) {
    o->fix (this) = true;
    o->val (this) = val;
  };

  friend struct Mopt;
  static Mopt table[];

public:
  Mopts ()
      : __start_of_options__ (Mopt ("__start_of_options__"))
#define OPTION(N, V, L, H, O, P, R, D) , N (Mopt (#N))
            OPTIONS
#undef OPTION
  {
    size_t i = 0;
#define OPTION(N, V, L, H, O, P, R, D) table[i] = Mopt (#N);
    OPTIONS
#undef OPTION
  };

  // Makes options directly accessible, e.g., for instance declares the
  // member 'int restart' here.  This will give fast access to option values
  // internally in the solver and thus can also be used in tight loops.
  //
private:
  Mopt __start_of_options__;

public:
#define OPTION(N, V, L, H, O, P, R, D) \
  Mopt N; // Access option values by name.
  OPTIONS
#undef OPTION

  // It would be more elegant to use an anonymous 'struct' of the actual
  // option values overlayed with an 'int values[number_of_options]' array
  // but that is not proper ISO C++ and produces a warning.  Instead we use
  // the following construction which relies on '__start_of_options__' and
  // that the following options are really allocated directly after it.
  //
  inline Mopt &val (size_t idx) {
    assert (idx < number_of_options);
    return (&__start_of_options__ + 1)[idx];
  }

  // With the following function we can get rather fast access to the option
  // limits, the default value and the description.  The code uses binary
  // search over the sorted option 'table'.  This static data is shared
  // among different instances of the solver.  The actual current option
  // values are here in the 'Mopts' class.  They can be accessed by the
  // offset of the static options using 'Mopt::val' if you have an
  // 'Mopt' or to have even faster access directly by the member function
  // (the 'N' above, e.g., 'restart').
  //
  static Mopt *has (const char *name) {
    size_t l = 0, r = number_of_options;
    while (l < r) {
      size_t m = l + (r - l) / 2;
      Mopt *res = &table[m];
      int tmp = strcmp (name, res->name);
      if (!tmp)
        return res;
      if (tmp < 0)
        r = m;
      if (tmp > 0)
        l = m + 1;
    }
    return 0;
  }

  // Explicit option value setting.

  bool set (const char *name, int val) {
    Mopt *o = has (name);
    if (!o)
      return false;
    set (o, val);
    return true;
  }

  int get (const char *name) {
    Mopt *o = has (name);
    return o ? o->val (this) : 0;
  }

  int get_fixed (const char *name) {
    Mopt *o = has (name);
    return o ? o->fix (this) : 0;
  }

  // Parse long option argument
  //
  //   (-F[ ])<name>
  //   (-F[ ])<name>=<val>
  //   (-F[ ])no-<name>
  //
  // where '<val>' is as in 'parse_option_value'.  If parsing succeeds,
  // 'true' is returned and the string will be set to the name of the
  // option.  Additionally the parsed value is set (last argument).
  //
  static bool parse_long_option (const char *arg, std::string &name,
                                 int &val) {
    if (arg[0] == '-')
      return false;
    const bool has_no_prefix =
        (arg[0] == 'n' && arg[1] == 'o' && arg[2] == '-');
    const size_t offset = has_no_prefix ? 3 : 0;
    name = arg + offset;
    const size_t pos = name.find_first_of ('=');
    if (pos != string::npos)
      name[pos] = 0;
    if (!Options::has (name.c_str ()))
      return false;
    if (pos == string::npos)
      val = !has_no_prefix;
    else {
      const char *val_str = name.c_str () + pos + 1;
      if (!parse_int_str (val_str, val))
        return false;
    }
    return true;
  };

  // Iterating options.

  typedef Mopt *iterator;
  typedef const Mopt *const_iterator;

  static iterator begin () { return table; }
  static iterator end () { return table + number_of_options; }
};

Mopt Mopts::table[] = {
#define OPTION(N, V, L, H, O, P, R, D) {#N},
    OPTIONS
#undef OPTION
};

inline int &Mopt::val (Mopts *opts) {
  assert (Mopts::table <= this && this < Mopts::table + number_of_options);
  return opts->val (this - Mopts::table).value;
}
inline bool &Mopt::fix (Mopts *opts) {
  assert (Mopts::table <= this && this < Mopts::table + number_of_options);
  return opts->val (this - Mopts::table).fixed;
}

/*------------------------------------------------------------------------*/

struct Shared {
  int64_t executed;
  int64_t solved;
  int64_t incremental;
  int64_t unsat;
  int64_t sat;
  int64_t memout;
  int64_t timeout;
  int64_t oom;

  struct {

#define STATISTIC(NAME, VERBOSE, COMMAND, OTHER, SYMBOL) int64_t NAME = 0;
#ifndef NMETRICS
#define METRIC(NAME, VERBOSE, COMMAND, SYMBOL, OTHER) Metric NAME = 0;
#else
#define METRIC(NAME, VERBOSE, COMMAND, SYMBOL, OTHER) ;
#endif

    CADICAL_STATISTICS

  } stats_sum;

  struct {

    CADICAL_STATISTICS

#undef STATISTIC
#undef METRIC

  } stats_count;

#ifdef MOBICAL_MEMORY
#define MOBICAL_MEMORY_STACK_COUNT 64
#define MOBICAL_MEMORY_LEAK_COUNT (1024 * 64)
  struct {
    size_t alloc_call_index;
    void *alloc_stack_array[MOBICAL_MEMORY_STACK_COUNT];
    size_t alloc_stack_size;
    size_t signal_call_index;
    void *signal_stack_array[MOBICAL_MEMORY_STACK_COUNT];
    size_t signal_stack_size;
  } bad_alloc;
  struct {
    size_t call_index[MOBICAL_MEMORY_LEAK_COUNT];
    size_t alloc_size[MOBICAL_MEMORY_LEAK_COUNT];
    void *alloc_ptr[MOBICAL_MEMORY_LEAK_COUNT];
    void
        *stack_array[MOBICAL_MEMORY_LEAK_COUNT][MOBICAL_MEMORY_STACK_COUNT];
    size_t stack_size[MOBICAL_MEMORY_LEAK_COUNT];
  } leak_alloc;
#endif

#ifdef MOBICAL_TERMINATE
#define MOBICAL_TERMINATE_STACK_COUNT 64
  struct {
    size_t terminate_call_index;
    void *terminate_stack_array[MOBICAL_TERMINATE_STACK_COUNT];
    size_t terminate_stack_size;
    size_t signal_call_index;
    void *signal_stack_array[MOBICAL_TERMINATE_STACK_COUNT];
    size_t signal_stack_size;
  } limit_terminate;
#endif
};

struct ExtendMap {
  // do we need to declare variable before using them?
  bool factor_check = true;
  // mapping of from literals of the trace to CaDiCaL's external literals
  vector<int> map;

  // either return the external literal from CaDiCaL, create one if
  // `declare_new_var` is one, or return any literal.
  int map_arg (Solver *s, int arg, bool declare_new_var = true) {
    const int abs_arg = abs (arg);
    const int sign = arg > 0 ? 1 : -1;
    const int map_size = map.size ();
    bool already_declared = (abs_arg < map_size && abs_arg && map[abs_arg]);
    if (!abs_arg) {
      assert (!map[abs_arg]);
      return 0;
    }
    if (already_declared) {
      return map[abs_arg] * sign;
    }
    if (declare_new_var) {
      extend_map_to (abs_arg);
      if (factor_check)
        map[abs_arg] = s->declare_one_more_variable ();
      else
        map[abs_arg] = s->vars () + 1;
      return map[abs_arg] * sign;
    }
    const int max_var = s->vars ();
    const int diff = abs_arg + map_size + 1;
    return sign * (max_var + diff);
  }

  // resize the internal map.
  void extend_map_to (int arg) {
    if (map.empty ())
      map.push_back (0); // 0 is always mapped to 0
    if (!arg)
      return;
    const unsigned abs_arg = abs (arg);
    if (abs_arg < map.size ())
      return; // arg is already mapped
    map.resize (abs_arg + 1, 0);
  }

  // extend the size of `extendmap` by `diff` new variables, mirroring
  // declare_more_variable API calls.
  //
  // Does not do anything if diff == 0.
  //
  // Important: this mimics the `declare_more_variable`, but does not call
  // `declare_more_variable`. It is the only place in this class where we
  // use our internal knowledge of the API.
  void extend_map_by (Solver *&s, int diff) {
    assert (diff >= 0);
    if (map.empty ())
      map.push_back (0); // 0 is always mapped to 0
    if (!diff)
      return;
    const int max_var = s->vars ();
    map.reserve (max_var + diff);
    for (int i = 1; i <= diff; i++)
      map.push_back (max_var + i);
  }
};

// Helper to print very verbose log during debugging

#ifdef LOGGING
#define MLOG(str) \
  do { \
    if (logging) \
      std::cout << "c [mock-propagator] " << str; \
  } while (false)
#define CLOG(str) \
  do { \
    if (logging) \
      std::cout << str; \
  } while (false)
#define RLOG(str) \
  do { \
    if (logging) \
      std::cout << "c [replay-propagator] " << str; \
  } while (false)
#define ILOG(...) \
  do { \
    Internal *internal = s->internal; \
    LOG (__VA_ARGS__); \
  } while (0)
#else
#define RLOG(str) \
  do { \
  } while (false)
#define MLOG(str) \
  do { \
  } while (false)
#define CLOG(str) \
  do { \
  } while (false)
#define ILOG(...) \
  do { \
  } while (false)
#endif

class MockPropagator;
class ReplayPropagator;

// This is the class for the Mobical application.

class Mobical : public Handler {

  /*----------------------------------------------------------------------*/

  friend class Reader;
  friend class Trace;
  friend class MockPropagator;
  friend class ReplayPropagator;
  friend struct Call;
  friend struct InitCall;
  friend struct FailedCall;
  friend struct ConcludeCall;
  friend struct ValCall;
  friend struct FlipCall;
  friend struct ImpliedCall;
  friend struct FlippableCall;
  friend struct MeltCall;
  friend struct ResetCall;
  friend struct ConnectCall;
  friend struct DisconnectCall;
  friend struct ObserveCall;
  friend struct UnObserveCall;
  friend struct ResetObservedCall;

  /*----------------------------------------------------------------------*/

  // We have the following modes, where 'RANDOM' mode can not be combined
  // with any other mode and 'OUTPUT' mode requires that 'SEED' or 'INPUT'
  // mode is set too, but it is not possible to combine 'SEED' and
  // 'INPUT'.

  enum { RANDOM = 1, SEED = 2, INPUT = 4, OUTPUT = 8 };

  int mode = 0; // No 'Mode mode' due to 'mode |= ...' below.

  void check_mode_valid ();

  /*----------------------------------------------------------------------*/

  // Global options (set by parsing command line options in 'main').

  DoNot donot;
  Force force;
  Mopts mopts;

  bool verbose = false;
  bool quiet = false;

  bool add_set_log_to_true = false;
  bool add_dump_before_solve = false;
  bool add_stats_after_solve = false;
  bool add_plain_after_options = false;

  /*----------------------------------------------------------------------*/

  bool shrinking = false; // In the middle of shrinking.
  bool running = false;   // In the middle of running.

  int64_t time_limit = DEFAULT_TIME_LIMIT;   // in seconds, none if zero
  int64_t space_limit = DEFAULT_SPACE_LIMIT; // in MB, none if zero
#ifdef MOBICAL_MEMORY
  bool bad_alloc = true;
  bool leak_alloc = true;
#endif
#ifdef MOBICAL_TERMINATE
  bool terminator = true;
#endif

  Terminal &terminal = terr;

  void header (); // Print right part of header.

  /*----------------------------------------------------------------------*/

  bool is_unsigned_str (const char *);
  uint64_t parse_seed (const char *);

  /*----------------------------------------------------------------------*/

  const char *prefix_string () {
    if (!terminal.colors ())
      return "m ";
    else
      return "\033[34mm \033[0m";
  }

  void prefix () {
    if (!quiet)
      cerr << prefix_string () << flush;
  }

  void error_prefix () {
    fflush (stderr);
    fflush (stdout);
    terminal.bold ();
    fputs ("mobical: ", stderr);
    terminal.normal ();
  }

  void hline ();      // print horizontal line
  void empty_line (); // print empty line

  /*----------------------------------------------------------------------*/

  void summarize (Trace &trace, bool bright = false);
  void progress (Trace &trace) { notify (trace, -1); }

  string notified;

#ifndef QUIET
  int progress_counter = 0;
  double last_progress_time = 0;
#endif

  void notify (Trace &trace, signed char ch = 0);

  /*----------------------------------------------------------------------*/

  Shared *shared; // shared among parent and child processes

  int64_t traces = 0;
  int64_t spurious = 0;

  void add_statistics (Solver *solver);
  void print_statistics ();
  void section (const char *);

  /*----------------------------------------------------------------------*/

  void die (const char *fmt, ...);
  void warning (const char *fmt, ...);

protected:
  /*----------------------------------------------------------------------*/

  MockPropagator
      *mock_pointer; // to be able to clean up withouth disconnect
  ReplayPropagator *replay_pointer;

public:
  Mobical ();
  ~Mobical ();

  void catch_signal (int); // Implement 'Handler'.

  int main (int, char **);
};

/*------------------------------------------------------------------------*/

CaDiCaL::Mobical mobical;

/*------------------------------------------------------------------------*/

// The mode invariant of the last comment can be checked with this code:

void Mobical::check_mode_valid () {
#ifndef NDEBUG
  assert (mode & (RANDOM | SEED | INPUT | OUTPUT));
  if (mode & RANDOM)
    assert (!(mode & SEED));
  if (mode & RANDOM)
    assert (!(mode & INPUT));
  if (mode & RANDOM)
    assert (!(mode & OUTPUT));
  if (mode & OUTPUT)
    assert (mode & (SEED | INPUT));
  assert (!((mode & SEED) && (mode & INPUT)));
#endif
}

/* As a formula this is

  (RANDOM | SEED | INPUT | OUTPUT) &
  (RANDOM -> !SEED)
  (RANDOM -> !INPUT) &
  (RANDOM -> !OUTPUT) &
  (OUTPUT -> SEED | INPUT) &
  !(SEED & INPUT)

It has exactly the following 5 out of 16 models

  RANDOM !SEED !INPUT !OUTPUT
  !RANDOM SEED !INPUT !OUTPUT
  !RANDOM SEED !INPUT OUTPUT
  !RANDOM !SEED INPUT OUTPUT
  !RANDOM !SEED INPUT !OUTPUT
*/

/*------------------------------------------------------------------------*/

void Mobical::die (const char *fmt, ...) {
  error_prefix ();
  terminal.red (true);
  fputs ("error: ", stderr);
  terminal.normal ();
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  terminal.reset ();
  exit (1);
}

void Mobical::warning (const char *fmt, ...) {
  error_prefix ();
  terminal.yellow ();
  fputs ("warning: ", stderr);
  terminal.normal ();
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
}

/*------------------------------------------------------------------------*/

// Abstraction of individual API calls.  The call sequences are assumed to
// have the following structure
//
//   INIT
//   (SET|TRACEPROOF|ALWAYS)*
//   (
//     (ADD|ASSUME|ALWAYS)*
//     [
//       (SOLVE|SIMPLIFY|LOOKAHEAD)
//       (LEMMA|FORCE|DECIDE)*
//       (VAL|FLIP|FAILED|ALWAYS|CONCLUDE|FLUSHPROOFTRACE|CLOSEPROOFTRACE)*
//     ]
//   )*
//   [ RESET ]
//
// where 'ALWAYS' calls as defined below do not change the state.  With
// the other short-cuts below we can abstract this to
//
//   CONFIG* (BEFORE* [ PROCESS DURING* AFTER* ] )* [ RESET ]
//
// If traces are read then they are checked to have this structure.  We
// check that 'ADD' sequences terminate by adding zero literal before
// another call is made ('ASSUME|ALWAYS|SOLVE|SIMPLIFY|LOOKAHEAD').
//
// Furthermore the execution engine (both for read and generated traces)
// makes sure that additional contract requirements are always met.  For
// instance 'val' is only executed if the solver is in the 'SATISFIABLE'
// state, and similar for 'failed', 'melt' etc.
//
// If the user wants to understand why a trace obtained through
// 'CADICAL_API_TRACE' is violating an API contract, then these checks
// are problematic and can be disabled by using the command line option
// '--do-not-enforce-contracts'.
//
// Note that our model based tester is actually more restrictive and does
// not produce all these possible call sequences. For instance it first
// adds all clauses before making assumptions and also does not mix in
// these 'ALWAYS' calls in all possible ways.

constexpr uint64_t shift (uint64_t bit) { return (uint64_t) 1 << bit; }

struct Call {

  enum Type : uint64_t {

    // clang-format off

    INIT                = shift (  0 ),
    RESET               = shift (  1 ),
    SET                 = shift (  2 ),
    CONFIGURE           = shift (  3 ),
                        
    VARS                = shift (  4 ),
    ACTIVE              = shift (  5 ),
    REDUNDANT           = shift (  6 ),
    IRREDUNDANT         = shift (  7 ),
    RESIZE              = shift (  8 ),
    DECLARE             = shift (  9 ),
    DECLARE_VARS        = shift ( 10 ),
    RESERVE             = shift ( 11 ),
                        
    PHASE               = shift ( 12 ),
    UNPHASE             = shift ( 13 ),
                        
    ADD                 = shift ( 14 ),
    ASSUME              = shift ( 15 ),
    CONSTRAIN           = shift ( 16 ),
    RESET_ASSUMPTIONS   = shift ( 17 ),
                        
    SOLVE               = shift ( 18 ),
    SIMPLIFY            = shift ( 19 ),
    LOOKAHEAD           = shift ( 20 ),
    CUBING              = shift ( 21 ),
    PROPAGATE           = shift ( 22 ),
    PROPAGATE_IMPLY     = shift ( 23 ),
                        
    VAL                 = shift ( 24 ),
    FLIP                = shift ( 25 ),
    FLIPPABLE           = shift ( 26 ),
    FAILED              = shift ( 27 ),
    FIXED               = shift ( 28 ),
    IMPLIED             = shift ( 29 ),
                        
    FREEZE              = shift ( 30 ),
    FROZEN              = shift ( 31 ),
    MELT                = shift ( 32 ),
                        
    LIMIT               = shift ( 33 ),
    OPTIMIZE            = shift ( 34 ),
                        
    DUMP                = shift ( 35 ),
    STATS               = shift ( 36 ),
                        
    CONNECT             = shift ( 37 ),
    OBSERVE             = shift ( 38 ),
    UNOBSERVE           = shift ( 39 ),
    RESET_OBSERVED      = shift ( 40 ),
    IS_DECISION         = shift ( 41 ),
    CURRENT_VALUE       = shift ( 42 ),
    
    LEMMA               = shift ( 43 ),
    DECIDE              = shift ( 44 ),
    FORCE               = shift ( 45 ),
    
    CB_DECIDE           = shift ( 46 ),
    CB_PROPAGATE        = shift ( 47 ),
    CB_HAS_CLAUSE       = shift ( 48 ),
    CB_ADD_CLAUSE       = shift ( 49 ),
    CB_ADD_REASON       = shift ( 50 ),
    CB_CHECK_MODEL      = shift ( 51 ),
    NOTIFY_ASSIGNMENT   = shift ( 52 ),
    NOTIFY_BACKTRACK    = shift ( 53 ),
    NOTIFY_LEVEL        = shift ( 54 ),

    CONCLUDE            = shift ( 55 ),
    DISCONNECT          = shift ( 56 ),
                        
    TRACEPROOF          = shift ( 57 ),
    FLUSHPROOFTRACE     = shift ( 58 ),
    CLOSEPROOFTRACE     = shift ( 59 ),

#ifdef MOBICAL_MEMORY
    MAXALLOC            = shift ( 60 ),
    LEAKALLOC           = shift ( 61 ),
#endif
#ifdef MOBICAL_TERMINATE
    TERMINATE           = shift ( 62 ),
#endif

    // clang-format on

    // These are used for contracts during parsing
    ALWAYS = VARS | ACTIVE | REDUNDANT | IRREDUNDANT | FREEZE | FROZEN |
             MELT | LIMIT | OPTIMIZE | DUMP | STATS | RESIZE | FIXED |
             PHASE | UNPHASE | RESERVE | OBSERVE | UNOBSERVE |
             RESET_OBSERVED | IS_DECISION | CURRENT_VALUE | DECLARE |
             DECLARE_VARS,
    MOCK = LEMMA | DECIDE | FORCE,
    REPLAY = CB_DECIDE | CB_PROPAGATE | CB_HAS_CLAUSE | CB_ADD_CLAUSE |
             NOTIFY_ASSIGNMENT | NOTIFY_BACKTRACK | NOTIFY_LEVEL,

    CONFIG = INIT | SET | CONFIGURE | ALWAYS | TRACEPROOF
#ifdef MOBICAL_MEMORY
             | MAXALLOC | LEAKALLOC
#endif
#ifdef MOBICAL_TERMINATE
             | TERMINATE
#endif
    ,
    BEFORE = ADD | CONSTRAIN | ASSUME | ALWAYS | DISCONNECT | CONNECT |
             RESET_ASSUMPTIONS,
    AFTER = VAL | FLIP | FLIPPABLE | FAILED | CONCLUDE | ALWAYS | IMPLIED |
            FLUSHPROOFTRACE | CLOSEPROOFTRACE,
    PROCESS =
        SOLVE | SIMPLIFY | LOOKAHEAD | CUBING | PROPAGATE | PROPAGATE_IMPLY,
    DURING = MOCK | REPLAY,

    // This is used for executing traces
    EXTENDMAP = PHASE | UNPHASE | ADD | ASSUME | FREEZE | CONSTRAIN,

    // These are used for shrinking traces
    CLAUSAL = LEMMA | CONSTRAIN | ADD,
    MATCHING = CONNECT | DISCONNECT,
    PROPAGATOR = OBSERVE | UNOBSERVE | RESET_OBSERVED | MOCK | REPLAY,
    LITTYPE = PHASE | UNPHASE | ADD | ASSUME | VAL | FLIP | FLIPPABLE |
              FAILED | FIXED | FREEZE | FROZEN | MELT | CONSTRAIN |
              UNOBSERVE | OBSERVE | LEMMA | DECIDE | FORCE,
    BASIC =
#ifdef MOBICAL_TERMINATE
        TERMINATE |
#endif
#ifdef MOBICAL_MEMORY
        LEAKALLOC | MAXALLOC |
#endif
        ASSUME | SOLVE | SIMPLIFY | LOOKAHEAD | CUBING | PROPAGATE |
        PROPAGATE_IMPLY | VARS | ACTIVE | REDUNDANT | IRREDUNDANT | RESIZE |
        RESERVE | VAL | FLIP | FLIPPABLE | FIXED | FAILED | FROZEN |
        CONCLUDE | FREEZE | MELT | PHASE | UNPHASE | LIMIT | OPTIMIZE |
        RESET_OBSERVED | DECIDE | FORCE | RESET_ASSUMPTIONS | OBSERVE |
        UNOBSERVE | IS_DECISION | CURRENT_VALUE,
  };

  Type type; // Explicit typing.

  int64_t res;          // Compute result if any.
  char *name = nullptr; // Option name for 'set' and 'config'
  int arg;              // Argument if necessary.
  int val;              // Option value for 'set'.
  bool executed;

  Call (Type t, int a = 0, int r = 0, const char *o = 0, int v = 0)
      : type (t), res (r), name (o ? strdup (o) : 0), arg (a), val (v),
        executed (0) {}

  virtual ~Call () {
    if (name)
      free (name);
  }

  virtual bool lit_type () {
    return (((uint64_t) type & (uint64_t) Call::LITTYPE)) != 0;
  }
  virtual bool extendmap_type () {
    return (((int) type & (int) Call::EXTENDMAP)) != 0;
  }
  virtual bool is_basic () {
    return (((uint64_t) type & (uint64_t) Call::BASIC)) != 0;
  }
  virtual bool is_clause_type () {
    return (((uint64_t) type & (uint64_t) Call::CLAUSAL)) != 0;
  }
  virtual bool config_type () {
    return (((uint64_t) type & (uint64_t) Call::CONFIG)) != 0;
  }
  virtual bool propagator_type () {
    return (((uint64_t) type & (uint64_t) Call::PROPAGATOR)) != 0;
  }
  virtual bool matching_type () {
    return (((uint64_t) type & (uint64_t) Call::MATCHING)) != 0;
  }
  virtual bool before_type () {
    return (((uint64_t) type & (uint64_t) Call::BEFORE)) != 0;
  }
  virtual bool during_type () {
    return (((uint64_t) type & (uint64_t) Call::DURING)) != 0;
  }
  virtual bool always_type () {
    return (((uint64_t) type & (uint64_t) Call::DURING)) != 0;
  }
  virtual bool process_type () {
    return (((uint64_t) type & (uint64_t) Call::PROCESS)) != 0;
  }
  virtual bool after_type () {
    return (((uint64_t) type & (uint64_t) Call::AFTER)) != 0;
  }

  // extend the size of `extendmap` by `arg` new variables.
  virtual void extend_map_by (Solver *&s, ExtendMap *&extendmap, int arg) {
    extendmap->extend_map_by (s, arg);
  }

  // extend the size of `extendmap` to reach size `std::abs (arg)`.
  virtual void extend_map_to (Solver *&s, ExtendMap *&extendmap) {
    extend_map_to (s, extendmap, arg);
  }
  // extend the size of `extendmap` to reach size `std::abs (arg)`.
  virtual void extend_map_to (Solver *&s, ExtendMap *&extendmap, int arg) {
    extendmap->extend_map_to (arg);
    (void) s;
  }

  virtual int map_arg (Solver *&s, ExtendMap *&extendmap,
                       bool declare_new_var = true) {
    if (!lit_type ())
      return arg;
    if (extendmap_type ())
      extend_map_to (s, extendmap);
    return extendmap->map_arg (s, arg, declare_new_var);
  }

  virtual void execute (Solver *&, ExtendMap *&, bool delay = false) {
    if (mobical.verbose) {
      if (delay)
        std::cout << "c [mobical] delaying call '";
      else
        std::cout << "c [mobical] executing call '";
      print (std::cout);
      std::cout << "'" << std::endl;
    }
    assert (!executed);
    executed = true;
  }
  virtual void print (ostream &o) = 0;
  virtual const char *keyword () = 0;
  virtual Call *copy () = 0;
};

/*------------------------------------------------------------------------*/

enum MockForceType {
  NOTIFY_ASSIGNMENT,
  NOTIFY_NEW_DECISION_LEVEL,
  NOTIFY_BACKTRACK,
  CB_DECIDE,
  CB_PROPAGATE,
  CB_CHECK_FOUND_MODEL,
  CB_HAS_EXTERNAL_CLAUSE,
  CB_ADD_EXTERNAL_CLAUSE_LIT,
  CB_ADD_REASON_CLAUSE_LIT,
  LAST_MOCK_FORCE_TYPE,
};

enum LemmaType {
  LAZY,
  PROPAGATING,
  OBSERVING,
  EAGER,
  LAST_LEMMA_TYPE,
};

static const char *ct_to_str (Call::Type type) {
  // clang-format off
  return (type == Call::CB_DECIDE ? "cb_decide"
       : (type == Call::CB_PROPAGATE ? "cb_propagate"
       : (type == Call::CB_CHECK_MODEL ? "cb_check_found_model"
       : (type == Call::CB_ADD_CLAUSE ? "cb_add_external_clause_lit"
       : (type == Call::CB_ADD_REASON ? "cb_add_reason_clause_lit"
       : (type == Call::CB_HAS_CLAUSE ? "cb_has_external_clause"
       : (type == Call::NOTIFY_ASSIGNMENT ? "notify_assignment"
       : (type == Call::NOTIFY_BACKTRACK ? "notify_backtrack"
       : (type == Call::NOTIFY_LEVEL ? "notify_level"
       : ((type & Call::ALWAYS) != 0 ? "ALWAYS"
       : "UNDEFINED"))))))))));
  // clang-format on
}

static const char *mft_to_str (MockForceType type) {
  // clang-format off
  return (type == NOTIFY_ASSIGNMENT ? "NOTIFY_ASSIGNMENT"
       : (type == NOTIFY_NEW_DECISION_LEVEL ? "NOTIFY_NEW_DECISION_LEVEL"
       : (type == NOTIFY_BACKTRACK ? "NOTIFY_BACKTRACK"
       : (type == CB_DECIDE ? "CB_DECIDE"
       : (type == CB_PROPAGATE ? "CB_PROPAGATE"
       : (type == CB_CHECK_FOUND_MODEL ? "CB_CHECK_FOUND_MODEL"
       : (type == CB_HAS_EXTERNAL_CLAUSE ? "CB_HAS_EXTERNAL_CLAUSE"
       : (type == CB_ADD_EXTERNAL_CLAUSE_LIT ? "CB_ADD_EXTERNAL_CLAUSE_LIT"
       : (type == CB_ADD_REASON_CLAUSE_LIT ? "CB_ADD_REASON_CLAUSE_LIT"
       : "LAST_MOCK_FORCE_TYPE")))))))));
  // clang-format on
}

class ReplayPropagator : public ExternalPropagator {
private:
  Solver *solver = 0;
  ExtendMap *extendmap = 0;

  // ReplayPropagator parameters
  bool logging = false;
  bool relaxed = 0;
  size_t current_action = 0;

  std::vector<Call *> cb_actions;

public:
  ReplayPropagator (Solver *s, ExtendMap *e, bool l, bool r)
      : solver (s), extendmap (e), logging (l), relaxed (r) {}

  ~ReplayPropagator () {
    for (auto &call : cb_actions) {
      delete call;
    }
  }
  void push_action (Call *c) { cb_actions.push_back (c); }

  void notify_assignment (const std::vector<int> &lits) override {
    if (!relaxed && cb_actions.size () <= current_action)
      fatal ("out of actions %zd in 'notify_assignment'", current_action);
    else if (cb_actions.size () <= current_action)
      return;
    assert (cb_actions.size () > current_action);
    Call *c = cb_actions[current_action++];
    while (c->always_type ()) {
      c->execute (solver, extendmap);
      assert (cb_actions.size () > current_action);
      c = cb_actions[current_action++];
    }
    if (!relaxed && c->type != Call::NOTIFY_ASSIGNMENT)
      fatal ("expected callback '%s' does not match 'notify_assignment'",
             ct_to_str (c->type));
    if (!relaxed && c->arg) {
      assert (c->val == 1);
      if (lits.size () != 1)
        fatal ("expected single assignment, not %zd", lits.size ());
      if (lits[0] != c->arg)
        fatal ("expected %d does not match assignment %d", c->val, lits[0]);
    } else if (!relaxed)
      fatal ("expected %d assignments, not %zd", c->val, lits.size ());
  }

  void notify_new_decision_level () override {
    if (!relaxed && cb_actions.size () <= current_action)
      fatal ("out of actions %zd in 'notify_new_decision_level'",
             current_action);
    else if (cb_actions.size () <= current_action)
      return;
    assert (cb_actions.size () > current_action);
    Call *c = cb_actions[current_action++];
    while (c->always_type ()) {
      c->execute (solver, extendmap);
      assert (cb_actions.size () > current_action);
      c = cb_actions[current_action++];
    }
    if (!relaxed && c->type != Call::NOTIFY_LEVEL)
      fatal ("expected callback '%s' does not match 'notify_assignment'",
             ct_to_str (c->type));
  }

  void notify_backtrack (size_t new_level) override {
    if (!relaxed && cb_actions.size () <= current_action)
      fatal ("out of actions %zd in 'notify_backtrack'", current_action);
    else if (cb_actions.size () <= current_action)
      return;
    assert (cb_actions.size () > current_action);
    Call *c = cb_actions[current_action++];
    while (c->always_type ()) {
      c->execute (solver, extendmap);
      assert (cb_actions.size () > current_action);
      c = cb_actions[current_action++];
    }
    if (!relaxed && c->type != Call::NOTIFY_BACKTRACK)
      fatal ("expected callback '%s' does not match 'notify_assignment'",
             ct_to_str (c->type));
    if (!relaxed && new_level != (size_t) c->val)
      fatal ("expected backtrack level %d does not match %zd", c->val,
             new_level);
  }

  bool cb_check_found_model (const std::vector<int> &model) override {
    (void) model;
    if (!relaxed && cb_actions.size () <= current_action)
      fatal ("out of actions %zd in 'cb_check_found_model'",
             current_action);
    else if (cb_actions.size () <= current_action)
      return 0;
    assert (cb_actions.size () > current_action);
    Call *c = cb_actions[current_action++];
    while (c->always_type ()) {
      c->execute (solver, extendmap);
      assert (cb_actions.size () > current_action);
      c = cb_actions[current_action++];
    }
    if (!relaxed && c->type != Call::CB_CHECK_MODEL)
      fatal ("expected callback '%s' does not match 'notify_assignment'",
             ct_to_str (c->type));
    else if (c->type == Call::CB_CHECK_MODEL)
      return c->res;
    return 0; // always return 0
  }

  int cb_decide () override {
    if (!relaxed && cb_actions.size () <= current_action)
      fatal ("out of actions %zd in 'cb_decide'", current_action);
    else if (cb_actions.size () <= current_action)
      return 0;
    assert (cb_actions.size () > current_action);
    Call *c = cb_actions[current_action++];
    while (c->always_type ()) {
      c->execute (solver, extendmap);
      assert (cb_actions.size () > current_action);
      c = cb_actions[current_action++];
    }
    if (!relaxed && c->type != Call::CB_DECIDE)
      fatal ("expected callback '%s' does not match 'notify_assignment'",
             ct_to_str (c->type));
    else if (c->type == Call::CB_DECIDE)
      return c->arg;
    return 0; // always return 0
  }

  int cb_propagate () override {
    if (!relaxed && cb_actions.size () <= current_action)
      fatal ("out of actions %zd in 'cb_propagate'", current_action);
    else if (cb_actions.size () <= current_action)
      return 0;
    assert (cb_actions.size () > current_action);
    Call *c = cb_actions[current_action++];
    while (c->always_type ()) {
      c->execute (solver, extendmap);
      assert (cb_actions.size () > current_action);
      c = cb_actions[current_action++];
    }
    if (!relaxed && c->type != Call::CB_PROPAGATE)
      fatal ("expected callback '%s' does not match 'notify_assignment'",
             ct_to_str (c->type));
    else if (c->type == Call::CB_PROPAGATE)
      return c->arg;
    return 0;
  }

  int cb_add_reason_clause_lit (int propagated_lit) override {
    (void) propagated_lit;
    if (!relaxed && cb_actions.size () <= current_action)
      fatal ("out of actions %zd in 'cb_add_reason_clause_lit'",
             current_action);
    else if (cb_actions.size () <= current_action)
      return 0;
    assert (cb_actions.size () > current_action);
    Call *c = cb_actions[current_action++];
    while (c->always_type ()) {
      c->execute (solver, extendmap);
      assert (cb_actions.size () > current_action);
      c = cb_actions[current_action++];
    }
    if (!relaxed && c->type != Call::CB_ADD_REASON)
      fatal ("expected callback '%s' does not match 'notify_assignment'",
             ct_to_str (c->type));
    else if (c->type == Call::CB_ADD_REASON)
      return c->arg;
    return 0;
  }

  bool cb_has_external_clause (bool &is_forgettable) override {
    (void) is_forgettable;
    if (!relaxed && cb_actions.size () <= current_action)
      fatal ("out of actions %zd in 'cb_has_external_clause'",
             current_action);
    else if (cb_actions.size () <= current_action)
      return 0;
    assert (cb_actions.size () > current_action);
    Call *c = cb_actions[current_action++];
    while (c->always_type ()) {
      c->execute (solver, extendmap);
      assert (cb_actions.size () > current_action);
      c = cb_actions[current_action++];
    }
    if (!relaxed && c->type != Call::CB_HAS_CLAUSE)
      fatal ("expected callback '%s' does not match 'notify_assignment'",
             ct_to_str (c->type));
    else if (c->type == Call::CB_HAS_CLAUSE)
      return c->res;
    return 0;
  }

  int cb_add_external_clause_lit () override {
    if (!relaxed && cb_actions.size () <= current_action)
      fatal ("out of actions %zd in 'cb_add_external_clause_lit'",
             current_action);
    else if (cb_actions.size () <= current_action)
      return 0;
    assert (cb_actions.size () > current_action);
    Call *c = cb_actions[current_action++];
    while (c->always_type ()) {
      c->execute (solver, extendmap);
      assert (cb_actions.size () > current_action);
      c = cb_actions[current_action++];
    }
    if (!relaxed && c->type != Call::CB_ADD_CLAUSE)
      fatal ("expected callback '%s' does not match 'notify_assignment'",
             ct_to_str (c->type));
    else if (c->type == Call::CB_ADD_CLAUSE)
      return c->arg;
    return 0;
  }
};

class MockPropagator : public ExternalPropagator,
                       public FixedAssignmentListener {
private:
  Solver *s = 0;
  ExtendMap *extendmap = 0;

  // MockPropagator parameters
  size_t lemma_per_cb = 2;
  bool logging = false;
  size_t level;

  struct Decisions {
    int lit;
    size_t delay;
    Decisions (int l, int d) : lit (l), delay (d) {};
  };

  struct MockForce {
    int lit;
    size_t delay;
    MockForce (int l, int d) : lit (l), delay (d) {};
  };

  struct ExternalLemma {
    size_t id;
    size_t add_count;
    size_t size;
    size_t next;

    int delay;

    LemmaType type;
    bool forgettable;
    bool tainting;
    bool propagation_reason;

    // Flexible array members are a C99 feature and not in C++11!
    // Thus pedantic compilation fails for 'int literals[]'.  We could do
    // the same conditional compilation as with the flexible array member
    // in 'Clause', but here there is no need for making it fast as we are
    // in testing mode anyhow.
    //
    int *literals;

    int *begin () { return literals; }
    int *end () { return literals + size; }

    int next_lit () {
      if (next < size)
        return literals[next++];
      else {
        next = 0;
        return 0;
      }
    }
  };

  // The list of all external lemmas (including reason clauses)
  std::vector<ExternalLemma *> external_lemmas;
  std::vector<Decisions> external_decide;
  std::unordered_map<MockForceType, std::vector<MockForce>> external_forces;

  // The reasons of present external propagations
  std::map<int, size_t> reason_map;
  std::map<int, size_t> level_map;
  std::map<int, bool> observed_map;
  std::map<int, signed char> value_map;
  std::vector<int> unnotified_propagations;

  // Next lemma to add
  size_t add_lemma_idx = 1;
  size_t propagate_idx = 0;

  // Forced lemme addition (falsified lemma in model)
  bool must_add_clause = false;
  size_t must_add_idx;

  // Observed variables and their current assignments
  std::deque<std::vector<int>> observed_trail;

  // Helpers
  size_t added_lemma_count = 0;
  size_t nof_clauses = 0;
  size_t nof_decide = 0;
  std::vector<int> clause;

  size_t add_new_lemma (bool forgettable, LemmaType type, int delay) {
    assert (clause.size () <= (size_t) INT_MAX);
    assert (external_lemmas.size () <= (size_t) INT_MAX);

    size_t size = clause.size ();
    ExternalLemma *lemma = new ExternalLemma;
    DeferDeletePtr<ExternalLemma> delete_lemma (lemma);
    lemma->literals = new int[size];
    DeferDeleteArray<int> delete_literals (lemma->literals);

    lemma->id = external_lemmas.size ();
    lemma->add_count = 0;
    lemma->size = size;
    lemma->next = 0;
    lemma->type = type;
    lemma->delay = delay;
    lemma->forgettable = forgettable;
    lemma->tainting = true;
    lemma->propagation_reason = false;

    int *q = lemma->literals;
    for (const auto &lit : clause)
      *q++ = lit;

    external_lemmas.push_back (lemma);
    delete_literals.release ();
    delete_lemma.release ();

    return lemma->id;
  }

  void extend_map (int arg) { extendmap->extend_map_to (arg); }

  int map_arg (int arg, bool declare_new_var = true) {
    return extendmap->map_arg (s, arg, declare_new_var);
  }

public:
  // It is public, so it can be shared easily between different
  // propagators
  std::vector<int> observed_fixed;

  MockPropagator (Solver *solver, ExtendMap *map,
                  bool with_logging = false) {
    observed_trail.push_back (std::vector<int> ());
    level = 0;
    s = solver;
    extendmap = map;
    logging = logging || with_logging;
    external_lemmas.push_back (nullptr);
  }

  ~MockPropagator () {
    for (auto l : external_lemmas)
      if (l)
        delete[] l->literals, delete l;
  }

  /*-----------------functions for mobical -----------------------------*/
  void push_decide_lit (int lit, int delay) {

    assert (lit != INT_MIN);
    nof_decide++;

    MLOG ("push decide to position " << external_decide.size ());
    CLOG (std::endl);

    external_decide.push_back (Decisions (lit, delay));
  }

  void push_force (int lit, MockForceType type, int delay) {
    external_forces[type].push_back (MockForce (lit, delay));
  }

  bool get_force (MockForceType type) {
    int lit = 0;
    if (external_forces[type].empty ())
      return false;
    if (external_forces[type].back ().delay--)
      return false;
    lit = external_forces[type].back ().lit;
    external_forces[type].pop_back ();
    MLOG ("activate force " << mft_to_str (type) << " on " << lit
                            << std::endl);
    bool res = 0;
    if (!observed_map[abs (lit)]) {
      res = true;
      add_observed (lit);
    }
    if (value_map[lit]) {
      res = true;
      s->force_unassign (lit);
    }
    return res;
  }

  void push_lemma_lit (int lit, LemmaType type, int delay) {

    if (lit)
      clause.push_back (lit);
    else {
      nof_clauses++;

      MLOG ("push lemma to position " << external_lemmas.size () << ": ");
      for (auto const &l : clause) {
        (void) l;
        CLOG (l << " ");
      }
      CLOG ("0" << std::endl);

      add_new_lemma (true, type, delay);
      clause.clear ();
    }
  }

  void add_observed (int lit) {
    if (observed_map[abs (lit)])
      return;
    assert (!value_map[lit]);
    assert (!s->observed (lit));
    observed_map[abs (lit)] = true;
    s->add_observed_var (lit);
  }

  void remove_observed (int lit) {
    if (!observed_map[abs (lit)])
      return;
    observed_map.erase (abs (lit));
    assert (s->observed (lit));
    auto it =
        std::find (observed_fixed.begin (), observed_fixed.end (), lit);
    if (it != observed_fixed.end ())
      observed_fixed.erase (it);
    if (value_map[lit]) {
      const int unit = lit * value_map[lit];
      // We are not necessarily at a synchonized point
      // assert (s->current_value (unit) > 0);
      auto level = level_map[lit];
      assert (observed_trail.size () > level);
      auto it = std::find (observed_trail[level].begin (),
                           observed_trail[level].end (), unit);
      assert (it != observed_trail[level].end ());
      observed_trail[level].erase (it);
      value_map[lit] = value_map[-lit] = 0;
      remove_reason (lit);
    }
    s->remove_observed_var (lit);
  }

  void reset_observed () {
    for (auto &kvp : observed_map) {
      if (!kvp.second)
        continue;
      const int lit = kvp.first;
      assert (s->observed (lit));
      value_map[lit] = value_map[-lit] = 0;
      remove_reason (lit);
    }
    observed_map.clear ();
    for (auto &t : observed_trail) {
      t.clear ();
    }
    observed_fixed.clear ();
    s->reset_observed_vars ();
  }

  void check_trail () {
    ILOG ("check consistency of mobical and solver assignments");
#ifndef NDEBUG
    for (auto &kvp : observed_map) {
      if (!kvp.second)
        continue;
      const int lit = kvp.first;
      assert (value_map[lit] == s->current_value (lit));
      assert (value_map[-lit] == s->current_value (-lit));
    }
#endif
  }
  void add_reason (int lit, ExternalLemma *lemma) {
    assert (!reason_map[lit]);
    lemma->propagation_reason = true;
    reason_map[lit] = lemma->id;
    unnotified_propagations.push_back (lit);
  }
  void remove_reason (int lit) {
    if (!reason_map[lit])
      return;
    size_t reason_id = reason_map[lit];
    assert (reason_id < external_lemmas.size ());
    external_lemmas[reason_id]->propagation_reason = false;
    external_lemmas[reason_id]->forgettable = true;
    reason_map.erase (lit);
  }

  /*-----------------functions for mobical ends ------------------------*/

  /*------------ FixedAssignmentListener functions ---------------------*/
  void notify_fixed_assignment (int lit) override {
    MLOG ("notify_fixed_assignment: "
          << lit << " (current level: " << observed_trail.size () - 1
          << ", current fixed count: " << observed_fixed.size () << ")"
          << std::endl);

    assert (std::find (observed_fixed.begin (), observed_fixed.end (),
                       lit) == observed_fixed.end ());
    observed_fixed.push_back (lit);
    // level_map[abs (lit)] = 0;
  };

  void add_prev_fixed (const std::vector<int> &fixed_assignments) {
    for (auto const &lit : fixed_assignments)
      notify_fixed_assignment (lit);
  }

  void collect_prev_fixed () {
#ifndef NDEBUG
    MLOG ("collecting previously fixed assignments for the new "
          "FixedAssignmentListener: ");

    std::vector<int> fixed_lits = {};
    s->internal->get_all_fixed_literals (fixed_lits);
    CLOG ("found: " << fixed_lits.size () << " fixed literals"
                    << std::endl);
    add_prev_fixed (fixed_lits);
    fixed_lits.clear ();
#endif
  }

  /* ----------- FixedAssignmentListener functions end -----------------*/

  /* -------------------- ExternalPropagator functions -----------------*/

  bool cb_check_found_model (const std::vector<int> &model) override {
    MLOG ("cb_check_found_model (" << model.size () << ") started" << endl);
    check_trail ();
#ifndef NDEBUG
    size_t assigned = model.size ();
    for (auto &level : observed_trail) {
      for (auto &lit : level) {
        // TODO: known bug that level 0 assigned literals can be
        // notified multiple times
        assert (assigned--);
        // unobserve calls can lead to unobserved variables in
        // observed_trail
        if (!s->observed (lit)) {
          assert (s->external->ival (abs (lit)) == lit);
          continue;
        }
        assert (s->current_value (lit) > 0);
      }
    }
#endif
    (void) model;

    // Calls to solver that might force it to backtrack.
    if (get_force (CB_CHECK_FOUND_MODEL))
      return false;

    for (const auto lemma : external_lemmas) {
      if (lemma == nullptr)
        continue;
      bool satisfied = false;
      int unobserved = 0;
      size_t level = 0;

      for (const auto lit : *lemma) {
        if (!lit)
          continue; // eoc
        if (!s->observed (lit)) {
          unobserved = lit;
          continue;
        }
        const signed char tmp = s->current_value (lit);
        if (tmp > 0) {
          satisfied = true;
          break;
        }
        if (level_map[lit] > level)
          level = level_map[lit];
        assert (tmp < 0);
      }
      if (unobserved && lemma->type == OBSERVING) {
        // this might trigger a bt
        add_observed (unobserved);
        return false;
      }

      if (unobserved)
        continue;

      if (!satisfied && lemma->type == PROPAGATING && level) {
        s->force_backtrack (level - 1);
        return false;
      }

      if (!satisfied) {
        assert (lemma->add_count == 0 || lemma->forgettable);

        must_add_clause = true;
        must_add_idx = lemma->id;

        MLOG ("false (external clause  "
              << lemma->id << "/" << external_lemmas.size ()
              << " is not satisfied: (forgettable: " << lemma->forgettable
              << ", size: " << lemma->size << "): ");
        for (auto const &l : *lemma) {
          CLOG (l << " ");
          (void) l;
        }
        CLOG (std::endl);

        MLOG ("cb_check_found_model (" << model.size () << ") returns: ");
        CLOG ("false" << std::endl);
        return false;
      }
    }

    MLOG ("cb_check_found_model (" << model.size () << ") returns: ");
    CLOG ("true" << std::endl);

    return true;
  }

  // Before finalizing the new ipasir-up
  bool cb_has_external_clause () {
    bool forgettable = true;
    return cb_has_external_clause (forgettable);
  }

  bool cb_has_external_clause (bool &forgettable) override {
    MLOG ("cb_has_external_clause returns: ");

    // Calls to solver that might force it to backtrack.
    get_force (CB_HAS_EXTERNAL_CLAUSE);

    forgettable = false;

    if (external_lemmas.size () == 1) {
      CLOG ("false (there are no external lemmas)." << std::endl);
      return false;
    }
    assert (external_lemmas.size () > 1);

    if (must_add_clause) {
      must_add_clause = false;
      add_lemma_idx = must_add_idx;

      forgettable = external_lemmas[must_add_idx]->forgettable;

      CLOG ("true (forced clause addition, "
            << "forgettable: " << forgettable << " id: " << add_lemma_idx
            << ")." << std::endl);

      added_lemma_count++;
      return true;
    }

    if (added_lemma_count > lemma_per_cb) {
      added_lemma_count = 0;
      CLOG ("false (lemma per CB treshold reached)." << std::endl);
      return false;
    }

    // Final model check will force to jump over some lemmas without
    // adding them. But if any of them is unsatisfied, it will force also
    // to set back the add_lemma_idx to them. So we do not need to start
    // the search here from 1.

    while (add_lemma_idx < external_lemmas.size ()) {

      auto lemma = external_lemmas[add_lemma_idx];
      assert (lemma != nullptr);
      if (!lemma->add_count && !lemma->propagation_reason &&
          lemma->type != PROPAGATING && lemma->type != LAZY &&
          !lemma->delay--) {

        external_lemmas[add_lemma_idx]->delay = 0;
        forgettable = external_lemmas[add_lemma_idx]->forgettable;

        CLOG ("true (new lemma was found, "
              << "forgettable: " << forgettable << " id: " << add_lemma_idx
              << ")." << std::endl);

        added_lemma_count++;
        return true;
      }

      // Forgettable lemmas are added repeatedly to the solver only when
      // the final model falsifies it (after cb_check_final_model).

      add_lemma_idx++;
    }
    if (add_lemma_idx >= external_lemmas.size ())
      add_lemma_idx = 1;
    CLOG ("false." << std::endl);

    return false;
  }

  int cb_add_external_clause_lit () override {
    // Calls to solver that might force it to backtrack.
    get_force (CB_ADD_EXTERNAL_CLAUSE_LIT);

    auto lemma = external_lemmas[add_lemma_idx];
    assert (lemma != nullptr);
    int lit = lemma->next_lit ();

    if (lemma->type == OBSERVING && lit && !s->observed (lit))
      add_observed (lit);
    while (lit && !s->observed (lit)) {
      MLOG ("cb_add_external_clause_lit "
            << lit << " (lemma " << add_lemma_idx << "/"
            << external_lemmas.size () << ") ignored as it is not observed"
            << std::endl);
      lit = lemma->next_lit ();
    }
    MLOG ("cb_add_external_clause_lit "
          << lit << " (lemma " << add_lemma_idx << "/"
          << external_lemmas.size () << ")" << std::endl);

    if (!lit)
      lemma->add_count++;

    return lit;
  }

  int cb_decide () override {
    MLOG ("cb_decide starts." << std::endl);
    check_trail ();
    // Calls to solver that might force it to backtrack.
    if (get_force (CB_DECIDE))
      return 0;

    if (external_decide.empty ()) {
      MLOG ("cb_decide returns 0" << std::endl);
      return 0;
    }

    auto &next_decision = external_decide.back ();
    if (next_decision.delay--) {
      MLOG ("cb_decide returns 0" << std::endl);
      return 0;
    }
    const int lit = next_decision.lit;
    external_decide.pop_back ();

    if (!lit) {
      MLOG ("cb_decide returns 0" << std::endl);
      return 0;
    }

    if (!s->observed (lit)) {
      // do we want to observe?
      add_observed (lit);
      MLOG ("cb_decide returns " << lit << std::endl);
      return lit;
    }

    if (s->current_value (lit) < 0) {
      MLOG ("cb_decide force_bt due to " << lit << std::endl);
      if (s->force_unassign (lit)) {
        // this decision is ignored, but we are asked again.
        MLOG ("cb_decide returns " << lit << std::endl);
        return lit;
      }
      MLOG ("cb_decide returns 0" << std::endl);
      return 0;
    }
    assert (s->current_value (lit) >= 0);
    if (s->current_value (lit) > 0) {
      MLOG ("cb_decide returns 0" << std::endl);
      return 0;
    }
    assert (!s->internal->val (s->external->internalize (lit)));
    MLOG ("cb_decide returns " << lit << std::endl);
    return lit;
  }

  int cb_propagate () override {
    MLOG ("cb_propagate starts" << std::endl);
    check_trail ();
    // Calls to solver that might force it to backtrack.
    if (get_force (CB_PROPAGATE))
      return 0;

    if (external_lemmas.size () <= 1)
      return 0;

    for (auto &lemma : external_lemmas) {
      // first lemma is 0 to have positive ids/indizes
      if (lemma == nullptr)
        continue;
      if (lemma->type != PROPAGATING)
        continue;
      if (lemma->propagation_reason)
        continue;
      int propagate = 0;
      int max = 0;
      for (auto &lit : *lemma) {
        const bool obs = s->observed (lit);
        if (!obs) {
          propagate = INT_MIN;
          break;
        }
        const signed char tmp = s->current_value (lit);
        if (tmp > 0) {
          propagate = INT_MIN;
          break;
        } else if (tmp < 0) {
          if (!max || level_map[abs (lit)] > level_map[abs (max)])
            max = lit;
          continue;
        } else if (propagate) {
          propagate = INT_MIN;
          break;
        }
        propagate = lit;
      }
      if (propagate == INT_MIN)
        continue;
      if (!propagate)
        propagate = max;
      if (!propagate)
        continue;
      if (lemma->delay) {
        lemma->delay--;
        continue;
      }
      add_reason (propagate, lemma);
      MLOG ("cb_propagate returns " << propagate << std::endl);
      return propagate;
    }

    MLOG ("cb_propagate returns 0" << std::endl);
    return 0;
  }

  int cb_add_reason_clause_lit (int plit) override {

    // Calls to solver that might force it to backtrack.
    // Not allowed here!
    // get_force (CB_ADD_REASON_CLAUSE_LIT);

    // At that point there is no need to assume that the trails are in
    // synchron.
    assert (reason_map[plit]);

    size_t reason_id = reason_map[plit];

    assert (reason_id);
    auto lemma = external_lemmas[reason_id];
    assert (lemma != nullptr);
    assert (lemma->type == PROPAGATING);
    int lit = lemma->next_lit ();

    if (!lit) {
      lemma->add_count++;
      MLOG ("reason clause for " << plit << " (id: " << reason_id
                                 << ") is added." << std::endl);
      assert (reason_map[plit]);
      remove_reason (plit);
    }

    return lit;
  }

  void notify_assignment (const std::vector<int> &lits) override {
    MLOG ("notified " << lits.size () << " new assignments on level "
                      << observed_trail.size () - 1 << std::endl);
    for (const auto &lit : lits) {
      observed_trail.back ().push_back (lit);
      level_map[abs (lit)] = level;
      value_map[lit] = 1;
      value_map[-lit] = -1;
      assert (s->current_value (lit) > 0);
    }
#ifndef NDEBUG
    for (auto &lit : unnotified_propagations) {
      assert (value_map[lit]);
      assert (level_map[abs (lit)] == level);
    }
#endif
    unnotified_propagations.clear ();
    // TODO: not correct with opts.extnassign
    // check_trail ();
    // Calls to solver that might force it to backtrack.
    get_force (NOTIFY_ASSIGNMENT);
  }

  void notify_new_decision_level () override {
    MLOG ("notify new decision level " << observed_trail.size () - 1
                                       << " -> " << observed_trail.size ()
                                       << std::endl);
    level++;
    observed_trail.push_back (std::vector<int> ());
    assert (level == observed_trail.size () - 1);
    check_trail ();
    // Calls to solver that might force it to backtrack.
    get_force (NOTIFY_NEW_DECISION_LEVEL);
  }

  void notify_backtrack (size_t new_level) override {
    MLOG ("notify backtrack: " << observed_trail.size () - 1 << " -> "
                               << new_level << std::endl);
    assert (observed_trail.size () > 1 || !new_level);
    assert (observed_trail.size () == 1 ||
            observed_trail.size () >= new_level + 1);
    while (observed_trail.size () > new_level + 1) {
      // TODO: We can not remove reason clauses of backtracked assignments
      // because ILB might re-introduces them to the trail. Here we only
      // save the potential candidates to delete, and upon next cb_decide
      // we delete those ones that did not get re-assigned.
      for (auto lit : observed_trail.back ()) {
        // assert (!reason_map[lit] || s->current_value (lit) <= 0);
        ILOG ("unassign %d (reason %zd/%zd)", lit, reason_map[lit],
              reason_map[-lit]);
        remove_reason (lit);
        value_map[lit] = value_map[-lit] = 0;
      }
      observed_trail.pop_back ();
    }
    level = new_level;
    for (auto &lit : unnotified_propagations) {
      remove_reason (lit);
    }
    unnotified_propagations.clear ();
    // Calls to solver that might force it to backtrack.
    // TODO: not allowed
    get_force (NOTIFY_BACKTRACK);
  }

  /* ----------- FixedAssignmentListener functions end -----------------*/
}; // namespace CaDiCaL

/*------------------------------------------------------------------------*/
// The model of valid API sequences is rather implicit.  First it is
// encoded in the random generator, by for instance adding options with
// 'set' only right after initialization through 'init', which is also
// enforced during parsing traces, but also in guards for executing
// certain API calls, marked 'CONTRACT' below.  For instance 'val' is only
// allowed if the solver is in the 'SATISFIED' state.

struct InitCall : public Call {
  InitCall () : Call (INIT) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    assert (!s);
    assert (!extendmap);
    try {
      s = new Solver ();
      extendmap = new ExtendMap ();
    } catch (std::bad_alloc &exception) {
      if (s)
        delete s;
      s = 0;
      throw exception;
    }
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new InitCall (); }
  const char *keyword () { return "init"; }
};

#ifdef MOBICAL_MEMORY
struct MaxAllocCall : public Call {
  MaxAllocCall (int val) : Call (MAXALLOC, 0, 0, 0, val) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    (void) s;
    (void) extendmap;
  }
  void print (ostream &o) { o << keyword () << " " << val; }
  Call *copy () { return new MaxAllocCall (val); }
  const char *keyword () { return "max_alloc"; }
};
struct LeakAllocCall : public Call {
  LeakAllocCall () : Call (LEAKALLOC) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    (void) s;
    (void) extendmap;
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new LeakAllocCall (); }
  const char *keyword () { return "leak_alloc"; }
};
#endif

#ifdef MOBICAL_TERMINATE
struct TerminateCall : public Call {
  TerminateCall (int val) : Call (TERMINATE, 0, 0, 0, val) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    (void) s;
    (void) extendmap;
  }
  void print (ostream &o) { o << keyword () << " " << val; }
  Call *copy () { return new TerminateCall (val); }
  const char *keyword () { return "terminate"; }
};
#endif

struct VarsCall : public Call {
  VarsCall () : Call (VARS) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else
      res = s->vars ();
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new VarsCall (); }
  const char *keyword () { return "vars"; }
};

struct ActiveCall : public Call {
  ActiveCall () : Call (ACTIVE) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else
      res = s->active ();
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new ActiveCall (); }
  const char *keyword () { return "active"; }
};

struct RedundantCall : public Call {
  RedundantCall () : Call (REDUNDANT) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else
      res = s->redundant ();
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new RedundantCall (); }
  const char *keyword () { return "redundant"; }
};

struct IrredundantCall : public Call {
  IrredundantCall () : Call (IRREDUNDANT) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else
      res = s->irredundant ();
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new IrredundantCall (); }
  const char *keyword () { return "irredundant"; }
};

struct ResizeCall : public Call {
  ResizeCall (int max_var) : Call (RESIZE, max_var) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else {
#ifndef NDEBUG
      bool has_effect = (s->vars () < arg && !arg);
#endif
      extend_map_to (s, extendmap);
      s->resize (arg);
#ifndef NDEBUG
      assert (!has_effect || extendmap->map.back () == s->vars ());
#endif
    }
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new ResizeCall (arg); }
  const char *keyword () { return "resize"; }
};

struct DeclareMoreVariablesCall : public Call {
  DeclareMoreVariablesCall (int max_var) : Call (DECLARE_VARS, max_var) {
    arg = max_var;
  }
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else {
      extend_map_by (s, extendmap, arg);
#ifndef NDEBUG
      int i =
#endif
          s->declare_more_variables (arg);
      // check that our mapping from trace literals to external literals
      // matchs the `declare_more_variables` result.
      assert (!arg || i == s->vars ());
      assert (!arg || extendmap->map.back () == i);
    }
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new DeclareMoreVariablesCall (arg); }
  const char *keyword () { return "declare_vars"; }
};

struct DeclareOneMoreVariableCall : public Call {
  DeclareOneMoreVariableCall () : Call (DECLARE) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else {
      extend_map_by (s, extendmap, 1);
#ifndef NDEBUG
      int i =
#endif
          s->declare_one_more_variable ();
      assert (i == s->vars ());
      assert (extendmap->map.back () == i);
    }
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new DeclareOneMoreVariableCall (); }
  const char *keyword () { return "declare_var"; }
};

struct UnPhaseCall : public Call {
  UnPhaseCall (int max_var) : Call (UNPHASE, max_var) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else
      s->unphase (map_arg (s, extendmap, false));
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new UnPhaseCall (arg); }
  const char *keyword () { return "unphase"; }
};

struct PhaseCall : public Call {
  PhaseCall (int max_var) : Call (PHASE, max_var) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else
      s->phase (map_arg (s, extendmap));
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new PhaseCall (arg); }
  const char *keyword () { return "phase"; }
};

struct SetCall : public Call {
  SetCall (const char *o, int v) : Call (SET, 0, 0, o, v) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    s->set (name, val);
    if (!strcmp (name, "factorcheck"))
      extendmap->factor_check = val;
  }
  void print (ostream &o) { o << keyword () << " " << name << ' ' << val; }
  Call *copy () { return new SetCall (name, val); }
  const char *keyword () { return "set"; }
};

struct ConfigureCall : public Call {
  ConfigureCall (const char *o) : Call (CONFIGURE, 0, 0, o) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    s->configure (name);
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword () << " " << name; }
  Call *copy () { return new ConfigureCall (name); }
  const char *keyword () { return "configure"; }
};

struct LimitCall : public Call {
  LimitCall (const char *o, int v) : Call (LIMIT, 0, 0, o, v) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else
      s->limit (name, val);
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword () << " " << name << ' ' << val; }
  Call *copy () { return new LimitCall (name, val); }
  const char *keyword () { return "limit"; }
};

struct OptimizeCall : public Call {
  OptimizeCall (int v) : Call (OPTIMIZE, 0, 0, 0, v) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else
      s->optimize (val);
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword () << " " << val; }
  Call *copy () { return new OptimizeCall (val); }
  const char *keyword () { return "optimize"; }
};

struct ResetCall : public Call {
  ResetCall () : Call (RESET) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    delete extendmap;
    delete s;
    s = 0;
    extendmap = 0;
    delete mobical.mock_pointer;
    mobical.mock_pointer = nullptr;
    delete mobical.replay_pointer;
    mobical.replay_pointer = nullptr;
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new ResetCall (); }
  const char *keyword () { return "reset"; }
};

struct AddCall : public Call {
  AddCall (int l) : Call (ADD, l) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    fflush (stdout);
    s->add (map_arg (s, extendmap));
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new AddCall (arg); }
  const char *keyword () { return "add"; }
};

struct ConstrainCall : public Call {
  ConstrainCall (int l) : Call (CONSTRAIN, l) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    s->constrain (map_arg (s, extendmap));
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new ConstrainCall (arg); }
  const char *keyword () { return "constrain"; }
};

struct ConnectCall : public Call {
  ConnectCall () : Call (CONNECT) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    // clean up if there was already one mock propagator
    if (!mobical.donot.mock_propagator) {
      assert (!mobical.mock_pointer);
#ifdef LOGGING
      mobical.mock_pointer =
          new MockPropagator (s, extendmap, mobical.add_set_log_to_true);
#else
      mobical.mock_pointer = new MockPropagator (s, extendmap);
#endif
      s->connect_external_propagator (mobical.mock_pointer);
      s->connect_fixed_listener (mobical.mock_pointer);

      // FixedAssignmentListener does not replay previous fixed
      // assignment, collect them here explicitly -- EXPENSIVE In practice
      // FixedAssignmentListener is there from the beginning if needed, in
      // mobical we do not want to wire in this.

      mobical.mock_pointer->collect_prev_fixed ();
    } else {
      assert (!mobical.replay_pointer);
      mobical.replay_pointer = new ReplayPropagator (
          s, extendmap, 0, mobical.donot.replay_strict);
      s->connect_external_propagator (mobical.replay_pointer);
    }
  }
  void print (ostream &o) {
    o << keyword () << " "
      << (mobical.donot.mock_propagator ? "replay-propagator"
                                        : "mock-propagator");
  }
  Call *copy () { return new ConnectCall (); }
  const char *keyword () { return "connect"; }
};

struct UnObserveCall : public Call {
  UnObserveCall (int l) : Call (OBSERVE, l) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (mobical.donot.mock_propagator) {
      if (delay) {
        ReplayPropagator *rp =
            static_cast<ReplayPropagator *> (s->get_propagator ());
        assert (rp);
        rp->push_action (copy ());
      } else {
        s->remove_observed_var (map_arg (s, extendmap));
      }
    } else {
      MockPropagator *mp =
          static_cast<MockPropagator *> (s->get_propagator ());
      assert (mp);
      mp->remove_observed (map_arg (s, extendmap));
    }
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new UnObserveCall (arg); }
  const char *keyword () { return "unobserve"; }
};

struct ObserveCall : public Call {
  ObserveCall (int l) : Call (OBSERVE, l) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    if (mobical.donot.mock_propagator) {
      if (delay) {
        ReplayPropagator *rp =
            static_cast<ReplayPropagator *> (s->get_propagator ());
        assert (rp);
        rp->push_action (copy ());
      } else {
        s->add_observed_var (map_arg (s, extendmap));
      }
    } else {
      Call::execute (s, extendmap, delay);
      MockPropagator *mp =
          static_cast<MockPropagator *> (s->get_propagator ());
      assert (mp);
      mp->add_observed (map_arg (s, extendmap));
    }
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new ObserveCall (arg); }
  const char *keyword () { return "observe"; }
};

struct CurrentValueCall : public Call {
  CurrentValueCall (int l, int r) : Call (CURRENT_VALUE, l, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else {
      s->current_value (map_arg (s, extendmap));
    }
  }
  void print (ostream &o) { o << keyword () << " " << arg << "" << res; }
  Call *copy () { return new CurrentValueCall (arg, res); }
  const char *keyword () { return "current_value"; }
};

struct IsDecisionCall : public Call {
  IsDecisionCall (int l, int r) : Call (IS_DECISION, l, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else {
      s->is_decision (map_arg (s, extendmap));
    }
  }
  void print (ostream &o) { o << keyword () << " " << arg << "" << res; }
  Call *copy () { return new IsDecisionCall (arg, res); }
  const char *keyword () { return "is_decision"; }
};

struct CBHasClauseCall : public Call {
  CBHasClauseCall (int r) : Call (CB_HAS_CLAUSE, 0, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (delay);
    Call::execute (s, extendmap, delay);
    ReplayPropagator *rp =
        static_cast<ReplayPropagator *> (s->get_propagator ());
    assert (rp);
    rp->push_action (copy ());
  }
  void print (ostream &o) { o << keyword () << " " << res; }
  Call *copy () { return new CBHasClauseCall (res); }
  const char *keyword () { return "cb_has_external_clause"; }
};

struct CBAddClauseCall : public Call {
  CBAddClauseCall (int l) : Call (CB_ADD_CLAUSE, l) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (delay);
    Call::execute (s, extendmap, delay);
    ReplayPropagator *rp =
        static_cast<ReplayPropagator *> (s->get_propagator ());
    assert (rp);
    rp->push_action (copy ());
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new CBAddClauseCall (arg); }
  const char *keyword () { return "cb_add_external_clause_lit"; }
};

struct CBAddReasonCall : public Call {
  CBAddReasonCall (int l) : Call (CB_ADD_CLAUSE, l) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (delay);
    Call::execute (s, extendmap, delay);
    ReplayPropagator *rp =
        static_cast<ReplayPropagator *> (s->get_propagator ());
    assert (rp);
    rp->push_action (copy ());
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new CBAddReasonCall (arg); }
  const char *keyword () { return "cb_add_reason_clause_lit"; }
};

struct CBCheckModelCall : public Call {
  CBCheckModelCall (int r) : Call (CB_CHECK_MODEL, 0, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (delay);
    Call::execute (s, extendmap, delay);
    ReplayPropagator *rp =
        static_cast<ReplayPropagator *> (s->get_propagator ());
    assert (rp);

    rp->push_action (copy ());
  }
  void print (ostream &o) { o << keyword () << " " << res; }
  Call *copy () { return new CBCheckModelCall (res); }
  const char *keyword () { return "cb_check_found_model"; }
};

struct CBPropagateCall : public Call {
  CBPropagateCall (int l) : Call (CB_PROPAGATE, l) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (delay);
    Call::execute (s, extendmap, delay);
    ReplayPropagator *rp =
        static_cast<ReplayPropagator *> (s->get_propagator ());
    assert (rp);
    rp->push_action (copy ());
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new CBPropagateCall (arg); }
  const char *keyword () { return "cb_propagate"; }
};

struct CBDecideCall : public Call {
  CBDecideCall (int l) : Call (CB_DECIDE, l) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (delay);
    Call::execute (s, extendmap, delay);
    ReplayPropagator *rp =
        static_cast<ReplayPropagator *> (s->get_propagator ());
    assert (rp);
    rp->push_action (copy ());
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new CBDecideCall (arg); }
  const char *keyword () { return "cb_decide"; }
};

struct NotifyAssignmentCall : public Call {
  NotifyAssignmentCall (int l) : Call (NOTIFY_ASSIGNMENT, l) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (delay);
    Call::execute (s, extendmap, delay);
    ReplayPropagator *rp =
        static_cast<ReplayPropagator *> (s->get_propagator ());
    assert (rp);
    rp->push_action (copy ());
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new NotifyAssignmentCall (arg); }
  const char *keyword () { return "notify_assignment"; }
};

struct NotifyBatchAssignmentCall : public Call {
  NotifyBatchAssignmentCall (int v)
      : Call (NOTIFY_ASSIGNMENT, 0, 0, 0, v) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (delay);
    Call::execute (s, extendmap, delay);
    ReplayPropagator *rp =
        static_cast<ReplayPropagator *> (s->get_propagator ());
    assert (rp);
    rp->push_action (copy ());
  }
  void print (ostream &o) { o << keyword () << " " << val; }
  Call *copy () { return new NotifyBatchAssignmentCall (val); }
  const char *keyword () { return "notify_assignment_batch"; }
};

struct NotifyBacktrackCall : public Call {
  NotifyBacktrackCall (int v) : Call (NOTIFY_BACKTRACK, 0, 0, 0, v) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (delay);
    Call::execute (s, extendmap, delay);
    ReplayPropagator *rp =
        static_cast<ReplayPropagator *> (s->get_propagator ());
    assert (rp);
    rp->push_action (copy ());
  }
  void print (ostream &o) { o << keyword () << " " << val; }
  Call *copy () { return new NotifyBacktrackCall (val); }
  const char *keyword () { return "notify_backtrack"; }
};

struct NotifyLevelCall : public Call {
  NotifyLevelCall () : Call (NOTIFY_LEVEL) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (delay);
    Call::execute (s, extendmap, delay);
    ReplayPropagator *rp =
        static_cast<ReplayPropagator *> (s->get_propagator ());
    assert (rp);
    rp->push_action (copy ());
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new NotifyLevelCall (); }
  const char *keyword () { return "notify_new_decision_level"; }
};

struct MockForceCall : public Call {
  MockForceType forcetype;
  MockForceCall (int l, MockForceType t, int v)
      : Call (FORCE, l, 0, 0, v), forcetype (t) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (delay);
    Call::execute (s, extendmap, delay);
    MockPropagator *mp =
        static_cast<MockPropagator *> (s->get_propagator ());
    assert (mp);
    mp->push_force (map_arg (s, extendmap, false), forcetype, val);
  }
  void print (ostream &o) {
    o << keyword () << " " << arg << " " << forcetype << " " << val;
  }
  Call *copy () { return new MockForceCall (arg, forcetype, val); }
  const char *keyword () { return "force"; }
};

struct LemmaCall : public Call {
  LemmaType lemmatype;
  LemmaCall (int l, LemmaType t, int v)
      : Call (LEMMA, l, 0, 0, v), lemmatype (t) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (delay);
    Call::execute (s, extendmap, delay);
    MockPropagator *mp =
        static_cast<MockPropagator *> (s->get_propagator ());
    assert (mp);
    mp->push_lemma_lit (map_arg (s, extendmap, false), lemmatype, val);
  }
  void print (ostream &o) {
    o << keyword () << " " << arg;
    if (!arg)
      o << " " << lemmatype << " " << val;
  }
  Call *copy () { return new LemmaCall (arg, lemmatype, val); }
  const char *keyword () { return "lemma"; }
};

struct DecideCall : public Call {
  DecideCall (int l, int v) : Call (DECIDE, l, 0, 0, v) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (delay);
    Call::execute (s, extendmap, delay);
    MockPropagator *mp =
        static_cast<MockPropagator *> (s->get_propagator ());
    assert (mp);
    mp->push_decide_lit (map_arg (s, extendmap, false), val);
  }
  void print (ostream &o) { o << keyword () << " " << arg << " " << val; }
  Call *copy () { return new DecideCall (arg, val); }
  const char *keyword () { return "decide"; }
};

struct DisconnectCall : public Call {
  DisconnectCall () : Call (DISCONNECT) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    if (mobical.donot.mock_propagator) {
      MockPropagator *mp =
          static_cast<MockPropagator *> (s->get_propagator ());
      assert (mp);
      s->disconnect_fixed_listener ();
      s->disconnect_external_propagator ();
      delete mp;
      mobical.mock_pointer = 0;
    } else {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      s->disconnect_external_propagator ();
      delete rp;
      mobical.replay_pointer = 0;
    }
    assert (!s->external->propagator);
    (void) (extendmap);
  }
  void print (ostream &o) {
    o << keyword () << " "
      << (mobical.donot.mock_propagator ? "replay-propagator"
                                        : "mock-propagator");
  }
  Call *copy () { return new DisconnectCall (); }
  const char *keyword () { return "disconnect"; }
};

struct AssumeCall : public Call {
  AssumeCall (int l) : Call (ASSUME, l) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    s->assume (map_arg (s, extendmap));
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new AssumeCall (arg); }
  const char *keyword () { return "assume"; }
};

struct SolveCall : public Call {
  SolveCall (int r = 0) : Call (SOLVE, 0, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    res = s->solve ();
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new SolveCall (res); }
  const char *keyword () { return "solve"; }
};

struct SimplifyCall : public Call {
  SimplifyCall (int rounds, int r = 0) : Call (SIMPLIFY, rounds, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    res = s->simplify (arg);
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword () << " " << arg << " " << res; }
  Call *copy () { return new SimplifyCall (arg, res); }
  const char *keyword () { return "simplify"; }
};

struct PropagateAssumptionsCall : public Call {
  PropagateAssumptionsCall (int r = 0) : Call (PROPAGATE, 0, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    s->propagate ();
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword () << " " << arg << " " << res; }
  Call *copy () { return new PropagateAssumptionsCall (arg); }
  const char *keyword () { return "propagate_assumptions"; }
};

struct ImpliedCall : public Call {
  ImpliedCall (int r = 0) : Call (IMPLIED, 0, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    std::vector<int> entrailed;
    if (mobical.donot.enforce || s->state () == State::SATISFIED ||
        s->state () == State::INCONCLUSIVE)
      s->implied (entrailed);
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new ImpliedCall (arg); }
  const char *keyword () { return "implied"; }
};

struct ResetAssumptionsCall : public Call {
  ResetAssumptionsCall () : Call (RESET_ASSUMPTIONS) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    s->reset_assumptions ();
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new ResetAssumptionsCall (); }
  const char *keyword () { return "reset_assumptions"; }
};

struct ResetObservedCall : public Call {
  ResetObservedCall () : Call (RESET_OBSERVED) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    MockPropagator *mp =
        static_cast<MockPropagator *> (s->get_propagator ());
    assert (mp);
    mp->reset_observed ();
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new ResetObservedCall (); }
  const char *keyword () { return "reset_observed"; }
};

struct LookaheadCall : public Call {
  LookaheadCall (int r = 0) : Call (LOOKAHEAD, 0, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    res = s->lookahead ();
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword () << " " << res; }
  Call *copy () { return new LookaheadCall (res); }
  const char *keyword () { return "lookahead"; }
};

struct CubingCall : public Call {
  CubingCall (int r = 1) : Call (CUBING, 0, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    (void) s->generate_cubes (arg);
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword () << " " << res; }
  Call *copy () { return new CubingCall (res); }
  const char *keyword () { return "cubing"; }
};

struct PropagateImplyCall : public Call {
  PropagateImplyCall (int r = 0) : Call (PROPAGATE_IMPLY, 0, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    (void) extendmap;
    int res = s->propagate ();
    if (!res) {
      std::vector<int> implicants;
      s->implied (implicants);
    }
  }
  void print (ostream &o) { o << keyword () << " " << res; }
  Call *copy () { return new PropagateImplyCall (res); }
  const char *keyword () { return "propagate"; }
};

struct ValCall : public Call {
  ValCall (int l, int r = 0) : Call (VAL, l, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    if (mobical.donot.enforce)
      res = s->val (map_arg (s, extendmap, false));
    else if (s->state () == SATISFIED)
      res = s->val (map_arg (s, extendmap, false));
    else
      res = 0;
  }
  void print (ostream &o) { o << keyword () << " " << arg << ' ' << res; }
  Call *copy () { return new ValCall (arg, res); }
  const char *keyword () { return "val"; }
};

struct FlipCall : public Call {
  FlipCall (int l, int r = 0) : Call (FLIP, l, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    if (mobical.donot.enforce)
      res = s->flip (map_arg (s, extendmap, false));
    else if (s->state () == SATISFIED)
      res = s->flip (map_arg (s, extendmap, false));
    else
      res = 0;
  }
  void print (ostream &o) { o << keyword () << " " << arg << ' ' << res; }
  Call *copy () { return new FlipCall (arg, res); }
  const char *keyword () { return "flip"; }
};

struct FlippableCall : public Call {
  FlippableCall (int l, int r = 0) : Call (FLIPPABLE, l, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    if (mobical.donot.enforce)
      res = s->flippable (map_arg (s, extendmap, false));
    else if (s->state () == SATISFIED)
      res = s->flippable (map_arg (s, extendmap, false));
    else
      res = 0;
  }
  void print (ostream &o) { o << keyword () << " " << arg << ' ' << res; }
  Call *copy () { return new FlipCall (arg, res); }
  const char *keyword () { return "flippable"; }
};

struct FixedCall : public Call {
  FixedCall (int l, int r = 0) : Call (FIXED, l, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else
      res = s->fixed (map_arg (s, extendmap, false));
  }
  void print (ostream &o) { o << keyword () << " " << arg << ' ' << res; }
  Call *copy () { return new FixedCall (arg, res); }
  const char *keyword () { return "fixed"; }
};

struct FailedCall : public Call {
  FailedCall (int l, int r = 0) : Call (FAILED, l, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    if (mobical.donot.enforce)
      res = s->failed (map_arg (s, extendmap, false));
    else if (s->state () == UNSATISFIED)
      res = s->failed (map_arg (s, extendmap, false));
    else
      res = 0;
  }
  void print (ostream &o) { o << keyword () << " " << arg << ' ' << res; }
  Call *copy () { return new FailedCall (arg, res); }
  const char *keyword () { return "failed"; }
};

struct ConcludeCall : public Call {
  ConcludeCall () : Call (CONCLUDE) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    if (mobical.donot.enforce)
      s->conclude ();
    else if (s->state () == UNSATISFIED || s->state () == SATISFIED)
      s->conclude ();
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new ConcludeCall (); }
  const char *keyword () { return "conclude"; }
};

struct FreezeCall : public Call {
  FreezeCall (int l) : Call (FREEZE, l) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else
      s->freeze (map_arg (s, extendmap));
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new FreezeCall (arg); }
  const char *keyword () { return "freeze"; }
};

struct MeltCall : public Call {
  MeltCall (int l) : Call (MELT, l) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else if (mobical.donot.enforce || s->frozen (map_arg (s, extendmap)))
      s->melt (map_arg (s, extendmap));
  }
  void print (ostream &o) { o << keyword () << " " << arg; }
  Call *copy () { return new MeltCall (arg); }
  const char *keyword () { return "melt"; }
};

struct FrozenCall : public Call {
  FrozenCall (int l, int r = 0) : Call (FROZEN, l, r) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    res = s->frozen (map_arg (s, extendmap, false));
  }
  void print (ostream &o) { o << keyword () << " " << arg << ' ' << res; }
  Call *copy () { return new FrozenCall (arg, res); }
  const char *keyword () { return "frozen"; }
};

struct DumpCall : public Call {
  DumpCall () : Call (DUMP) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    s->dump_cnf ();
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new DumpCall (); }
  const char *keyword () { return "dump"; }
};

struct StatsCall : public Call {
  StatsCall () : Call (STATS) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    Call::execute (s, extendmap, delay);
    if (delay) {
      ReplayPropagator *rp =
          static_cast<ReplayPropagator *> (s->get_propagator ());
      assert (rp);
      rp->push_action (copy ());
    } else
      s->statistics ();
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new StatsCall (); }
  const char *keyword () { return "stats"; }
};

struct TraceProofCall : public Call {
  std::string path;
  TraceProofCall (const string &p) : Call (TRACEPROOF), path (p) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    s->trace_proof (path.c_str ());
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword () << " " << path; }
  Call *copy () { return new TraceProofCall (path); }
  const char *keyword () { return "trace_proof"; }
};

struct FlushProofTraceCall : public Call {
  FlushProofTraceCall () : Call (FLUSHPROOFTRACE) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    s->flush_proof_trace ();
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new FlushProofTraceCall (); }
  const char *keyword () { return "flush_proof_trace"; }
};

struct CloseProofTraceCall : public Call {
  CloseProofTraceCall () : Call (CLOSEPROOFTRACE) {}
  void execute (Solver *&s, ExtendMap *&extendmap, bool delay = false) {
    assert (!delay);
    Call::execute (s, extendmap, delay);
    s->close_proof_trace ();
    (void) (extendmap);
  }
  void print (ostream &o) { o << keyword (); }
  Call *copy () { return new CloseProofTraceCall (); }
  const char *keyword () { return "close_proof_trace"; }
};

/*------------------------------------------------------------------------*/

class Trace
#ifdef MOBICAL_TERMINATE
    : public Terminator
#endif
{

  int64_t id;
  uint64_t seed;

  // map from mobical vars to solver vars (skipping extension variables)
  // the map is strictly increasing and gets updated whenever a call with
  // an argument gets executed.
  Solver *solver;
  ExtendMap *extendmap;

  vector<Call *> calls;

  friend class Reader;

public:
  static int64_t generated;
  static int64_t executed;
  static int64_t failed;
  static int64_t ok;

  static int64_t trace_call_index;

#ifdef MOBICAL_MEMORY
  static int64_t memory_bad_alloc;
  static int64_t memory_bad_size;
  static int64_t memory_bad_failed;
  static int64_t memory_leak_alloc;
  static int64_t memory_leak_next_free;
#endif

#ifdef MOBICAL_TERMINATE
  static int64_t limit_terminate;
  static int64_t limit_terminate_remaining;
  bool terminate () override {
    // Send termination signal once when counter reaches 0.
    if (!limit_terminate || !limit_terminate_remaining)
      return false;
    if (--limit_terminate_remaining > 0u)
      return false;

    mobical.shared->limit_terminate.terminate_call_index = trace_call_index;
    mobical.shared->limit_terminate.terminate_stack_size =
        backtrace (mobical.shared->limit_terminate.terminate_stack_array,
                   MOBICAL_TERMINATE_STACK_COUNT);
    return true;
  }
#endif

#define SIGNALS \
  SIGNAL (SIGINT) \
  SIGNAL (SIGSEGV) \
  SIGNAL (SIGABRT) \
  SIGNAL (SIGTERM) \
  SIGNAL (SIGBUS) \
  SIGNAL (SIGUSR1) \
  SIGNAL (SIGUSR2) \
  SIGNAL (SIGTSTP)

#define SIGNAL(SIG) static void (*old_##SIG##_handler) (int);
  SIGNALS
#undef SIGNAL
  static void child_signal_handler (int);
  static void init_child_signal_handlers ();
  static void reset_child_signal_handlers ();

#ifdef MOBICAL_MEMORY
#define MOBICAL_PRINT_TRACE
  static void hooks_install (void);
  static void hooks_uninstall (void);
  static void *hook_malloc (size_t);
  static void *hook_realloc (void *, size_t);
  static void hook_free (void *);
#endif

#ifdef MOBICAL_TERMINATE
#define MOBICAL_PRINT_TRACE
#endif

#ifdef MOBICAL_PRINT_TRACE
  static void print_trace (void **, size_t, ostream &, size_t);
#endif

  Trace (int64_t i = 0, uint64_t s = 0)
      : id (i), seed (s), solver (0), extendmap (0) {}

  void clear () {
    while (!calls.empty ()) {
      Call *c = calls.back ();
      delete c;
      calls.pop_back ();
    }
    if (solver) {
      if (!mobical.donot.summary && mobical.shared) {
        mobical.add_statistics (solver);
      }
      delete solver;
      delete extendmap;
    }
    solver = 0;
    extendmap = 0;
  }

  ~Trace () { clear (); }

  void push_back (Call *c) { calls.push_back (c); }

  void print (ostream &o, int code) {
    if (seed)
      o << "# seed: " << seed << endl;

    if (code == 1)
      o << "# status: exited with error or assertion thrown"
           " (1 / SIGABRT)"
        << endl;
    else if (code == 2)
      o << "# status: resource limit reached (2 / SIGXCPU)" << endl;
    else if (code == 3)
      o << "# status: forced bad allocation lead to crash / assertion"
           " (3 / SIGUSR1)"
        << endl;
    else if (code == 4)
      o << "# status: solver was destructed, but memory leaked"
           " (4 / SIGUSR2)"
        << endl;
    else if (code == 5)
      o << "# status: termination request lead to crash / assertion"
           " (5 / SIGTSTP)"
        << endl;
    else if (code == 6)
      o << "# status: unknown signal was raised (6)" << endl;
    else {
      o << "# "
           "------------------------------------------------------------"
        << endl;
      o << "# status: ok, exited with code " << code << endl;
      o << "#" << endl;
      for (int i = 0; i < 20; i++)
        o << "# WARNING: THIS TRACE PROBABLY HAS NOTHING TO DEBUG "
             "(SPURIOUS)"
          << endl;
      o << "#" << endl;
      o << "# "
           "------------------------------------------------------------"
        << endl;
    }

    for (size_t i = 0; i < calls.size (); i++) {
#ifdef MOBICAL_MEMORY
      for (size_t index{0u}; index < MOBICAL_MEMORY_LEAK_COUNT; index++) {
        if (mobical.shared->leak_alloc.call_index[index] == i + 1) {
          o << "# V------------------------------------------------------"
               "---------------- leak alloc: leaked allocation"
            << endl;
          break;
        }
      }
      if (mobical.shared->bad_alloc.alloc_call_index == i + 1)
        o << "# V--------------------------------------------------------"
             "-------------- bad alloc: failed allocation"
          << endl;
      if (mobical.shared->bad_alloc.signal_call_index == i + 1)
        o << "# V--------------------------------------------------------"
             "-------------- bad alloc: crashed / assertion"
          << endl;
#endif
#ifdef MOBICAL_TERMINATE
      if (mobical.shared->limit_terminate.terminate_call_index == i + 1)
        o << "# V--------------------------------------------------------"
             "-------------- terminate: termination requested"
          << endl;
      if (mobical.shared->limit_terminate.signal_call_index == i + 1)
        o << "# V--------------------------------------------------------"
             "-------------- terminate: crashed / assertion"
          << endl;
#endif
      o << i << ' ';
      calls[i]->print (o);
#ifdef MOBICAL_MEMORY
      if ((mobical.shared->bad_alloc.alloc_call_index != 0) &&
          (mobical.shared->bad_alloc.alloc_call_index < i + 1) &&
          (calls[i]->type != Call::RESET)) {
        o << " # <----------- ignored";
      }
#endif
      o << endl;
    }

#ifdef MOBICAL_MEMORY
    if (mobical.shared->bad_alloc.alloc_call_index > 0) {
      o << "# ---------------------------------------------------" << endl;
      o << "# Memory was tried to be allocated here:" << endl;
      assert (mobical.shared->bad_alloc.alloc_stack_size <=
              MOBICAL_MEMORY_STACK_COUNT);
      print_trace (mobical.shared->bad_alloc.alloc_stack_array,
                   mobical.shared->bad_alloc.alloc_stack_size, o, 0);
      o << "#" << endl;
    }
    if (mobical.shared->bad_alloc.signal_call_index > 0) {
      o << "# ---------------------------------------------------" << endl;
      o << "# A crash / assertion happened here:" << endl;
      assert (mobical.shared->bad_alloc.signal_stack_size <=
              MOBICAL_MEMORY_STACK_COUNT);
      print_trace (mobical.shared->bad_alloc.signal_stack_array,
                   mobical.shared->bad_alloc.signal_stack_size, o, 0);
      o << "#" << endl;
    }
    for (size_t index{0u}; index < MOBICAL_MEMORY_LEAK_COUNT; index++) {
      if (mobical.shared->leak_alloc.alloc_ptr[index] != nullptr) {
        o << "# ---------------------------------------------------"
          << endl;
        o << "# Leak of " << mobical.shared->leak_alloc.alloc_size[index]
          << " bytes at (0x" << hex << setw (64 / 4) << setfill ('0')
          << mobical.shared->leak_alloc.alloc_ptr[index] << dec << ")"
          << endl;
        o << "# Memory was allocated here:" << endl;
        assert (mobical.shared->leak_alloc.stack_size[index] <=
                MOBICAL_MEMORY_STACK_COUNT);
        print_trace (mobical.shared->leak_alloc.stack_array[index],
                     mobical.shared->leak_alloc.stack_size[index], o, 0);
        o << "#" << endl;
      }
    }
#endif
#ifdef MOBICAL_TERMINATE
    if (mobical.shared->limit_terminate.terminate_call_index > 0) {
      o << "# ---------------------------------------------------" << endl;
      o << "# CaDiCal was tried to be terminated here:" << endl;
      assert (mobical.shared->limit_terminate.terminate_stack_size <=
              MOBICAL_TERMINATE_STACK_COUNT);
      print_trace (mobical.shared->limit_terminate.terminate_stack_array,
                   mobical.shared->limit_terminate.terminate_stack_size, o,
                   0);
      o << "#" << endl;
    }
    if (mobical.shared->limit_terminate.signal_call_index > 0) {
      o << "# ---------------------------------------------------" << endl;
      o << "# A crash / assertion happened here:" << endl;
      assert (mobical.shared->limit_terminate.signal_stack_size <=
              MOBICAL_TERMINATE_STACK_COUNT);
      print_trace (mobical.shared->limit_terminate.signal_stack_array,
                   mobical.shared->limit_terminate.signal_stack_size, o, 0);
      o << "#" << endl;
    }
#endif
  }

  void execute () {
#ifdef MOBICAL_MEMORY
    memory_bad_alloc = 0;
    memory_bad_size = 0;
    memory_bad_failed = 0;
    memory_leak_alloc = 0;
    memory_leak_next_free = 0;
    std::memset (&mobical.shared->bad_alloc, 0,
                 sizeof (mobical.shared->bad_alloc));
    std::memset (&mobical.shared->leak_alloc, 0,
                 sizeof (mobical.shared->leak_alloc));
    hooks_install ();
#endif
#ifdef MOBICAL_TERMINATE
    limit_terminate = 0;
    limit_terminate_remaining = 0;
#endif

    executed++;
    bool first = true;
    bool deallocated = false;
    for (size_t i = 0; i < calls.size (); i++) {
      Call *c = calls[i];
      trace_call_index = i + 1;

#ifdef MOBICAL_MEMORY
      if (memory_bad_failed && c->type != Call::RESET) {
        continue; // Ignore call, only RESET (deallocation) allowed.
      }
#else
      (void) deallocated;
#endif

      try {
        // They are (ideally) are executed already
        if (c->executed) {
          assert (c->during_type () || c->always_type ());
          continue;
        }
        assert (!c->during_type ());
#ifdef MOBICAL_MEMORY
        if (c->type == Call::MAXALLOC) {
          memory_bad_alloc = c->val;
          memory_bad_size = 0;
          continue;
        } else if (c->type == Call::LEAKALLOC) {
          memory_leak_alloc = 1;
          memory_leak_next_free = 0;
          continue;
        } else if (c->type == Call::RESET) {
          // Set the flag before the reset call such that memory leaks
          // are found when the reset call leaks memory.
          deallocated = true;
        }
#endif
#ifdef MOBICAL_TERMINATE
        if (c->type == Call::TERMINATE) {
          limit_terminate = 1;
          limit_terminate_remaining = c->val;
        }
#endif

        if (c->type == Call::SET) {
          // ignore fixed options
          if (mobical.mopts.get_fixed (c->name))
            continue;
        }
        if (c->process_type ()) {
          // Look ahead and collect LemmaCalls to be executed
          // before solve is executed
          for (size_t j = i + 1; j < calls.size (); j++) {
            Call *next_c = calls[j];
            if (next_c->during_type ())
              next_c->execute (solver, extendmap, true);
            else if (mobical.donot.mock_propagator &&
                     next_c->always_type ()) {
              bool during = false;
              for (size_t k = j + 1; k < calls.size (); k++) {
                Call *next_next_c = calls[k];
                while (next_next_c->always_type ())
                  continue;
                if (next_next_c->during_type ())
                  during = true;
                break;
              }
              if (during) {
                while (next_c->always_type ()) {
                  next_c->execute (solver, extendmap, true);
                  next_c = calls[++j];
                }
                assert (next_c->during_type ());
                next_c->execute (solver, extendmap, true);
              } else
                break;
            } else
              break;
          }
        }
        if (!mobical.donot.summary && mobical.shared &&
            c->type == Call::RESET) {
          if (solver)
            mobical.add_statistics (solver);
          mobical.shared->executed++;
        }
        if (mobical.shared && c->process_type ()) {
          mobical.shared->solved++;
          if (first)
            first = false;
          else
            mobical.shared->incremental++;
          c->execute (solver, extendmap);
          if (c->res == 10)
            mobical.shared->sat++;
          if (c->res == 20)
            mobical.shared->unsat++;
        } else
          c->execute (solver, extendmap);
        // initialize options after INIT or CONFIGURE
        if (c->type == Call::INIT || c->type == Call::CONFIGURE) {
#ifdef MOBICAL_TERMINATE
          // Connect terminator but never disconnect it
          // (might violate API contract on failed allocation).
          solver->connect_terminator (this);
#endif
          for (auto &o : mobical.mopts) {
            if (o.fix (&mobical.mopts)) {
              solver->set (o.name, o.val (&mobical.mopts));
              if (!strcmp (o.name, "factorcheck"))
                extendmap->factor_check = o.val (&mobical.mopts);
            }
          }
        }
      } catch (const std::bad_alloc &e) {
        // Ignore out-of-memory errors and assume solver state is
        // consistent. Only reset calls (destruction of the solver)
        // are allowed after a bad allocation caused by the bad_alloc call
        // or by CaDiCaL running out of memory due to process limitations.
        mobical.shared->oom++;
#ifdef MOBICAL_MEMORY
        if (!memory_bad_failed) {
          memory_bad_failed = 1;
          mobical.shared->bad_alloc.alloc_call_index = trace_call_index;
          mobical.shared->bad_alloc.alloc_stack_size = 0;
        }
#endif
      }
    }

#ifdef MOBICAL_MEMORY
    // Delete the mock pointer to ignore these memory leaks
    // in case the reset call failed due to a bad memory allocation.
    if (deallocated) {
      delete mobical.mock_pointer;
      mobical.mock_pointer = nullptr;
      delete mobical.replay_pointer;
      mobical.replay_pointer = nullptr;
    }
    hooks_uninstall ();
    // Note: Do not force-deallocate the solver here as otherwise
    // the shrink procedure will remove the RESET call.
    if (deallocated) {
      for (size_t index{0u}; index < MOBICAL_MEMORY_LEAK_COUNT; index++) {
        if (mobical.shared->leak_alloc.alloc_ptr[index] != nullptr) {
          reset_child_signal_handlers ();
          raise (SIGUSR2);
        }
      }
    } else {
      // If reset was not called before reaching here (deallocated is not
      // set) the leaks are false positives. In this case clear all the
      // leaks. Otherwise, the user will get leaked memory warnings even
      // though the memory is not freed since no reset call is present.
      for (size_t index{0u}; index < MOBICAL_MEMORY_LEAK_COUNT; index++) {
        mobical.shared->leak_alloc.alloc_ptr[index] = nullptr;
      }
    }
#endif
  }

  int vars () {
    int res = 0;
    for (size_t i = 0; i < calls.size (); i++) {
      Call *c = calls[i];
      int tmp = abs (c->arg);
      if (tmp > res)
        res = tmp;
    }
    return res;
  }

  int64_t clauses () {
    int64_t res = 0;
    for (size_t i = 0; i < calls.size (); i++) {
      Call *c = calls[i];
      if (c->type == Call::ADD && !c->arg)
        res++;
    }
    return res;
  }

  int64_t literals () {
    int64_t res = 0;
    for (size_t i = 0; i < calls.size (); i++) {
      Call *c = calls[i];
      if (c->type == Call::ADD && c->arg)
        res++;
    }
    return res;
  }

  int64_t phases () {
    int64_t res = 0;
    bool last = true;
    for (size_t i = 0; i < calls.size (); i++) {
      Call *c = calls[i];
      if (last && c->type != Call::VAL && c->type != Call::FLIP &&
          c->type != Call::FLIPPABLE && c->type != Call::FAILED &&
          c->type != Call::FROZEN && c->type != Call::RESET)
        res++, last = false;
      if (c->process_type ())
        last = true;
    }
    return res;
  }

  size_t size () { return calls.size (); }
  Call *operator[] (size_t i) { return calls[i]; }

  void generate (uint64_t id, uint64_t seed);

  int fork_and_execute ();
  void shrink (int expected);

  void write_prefixed_seed (const char *prefix, int code);
  void write_path (const char *path, int code);

  static bool ignored_option (const char *name);
  bool ignore_option (const char *, int max_var);
  int64_t option_high_value (const char *, int64_t def, int64_t lo,
                             int64_t hi);

private:
  void notify (char ch = 0) { mobical.notify (*this, ch); }
  void progress () { mobical.progress (*this); }
  void progress (Trace &tmp) { mobical.progress (tmp); }

  struct Segment {
    size_t lo, hi;
    Segment (size_t l, size_t h) : lo (l), hi (h) {
      assert (0 < l), assert (l < h);
    }
  };

  typedef vector<Segment> Segments;
  bool shrink_segments (Segments &, int expected);

  vector<int> observed_vars;
  bool in_connection = false;

  void add_options (int expected);
  bool shrink_phases (int expected);
  bool shrink_propagator (int expected);
  bool shrink_clauses (int expected);
  bool shrink_literals (int expected);
  bool shrink_basic (int expected);
  bool shrink_disable (int expected);
  bool reduce_values (int expected);
  void map_variables (int expected);
  void shrink_options (int expected);

  size_t first_option ();
  size_t last_option ();

  Call *find_option_by_prefix (const char *name);
  Call *find_option_by_name (const char *name);

  void generate_options (Random &, Size);
  void generate_queries (Random &);
  void generate_resize (Random &, int vars);
  void generate_declare_one_more_variable (Random &);
  void generate_declare_more_variables (Random &);
  void generate_clause (Random &, int minvars, int maxvars, int uniform);
  void generate_constraint (Random &, int minvars, int maxvars,
                            int uniform);
  void generate_assume (Random &, int vars);
  void generate_process (Random &);
  void generate_values (Random &, int vars);
  void generate_flipped (Random &, int vars);
  void generate_frozen (Random &, int vars);
  void generate_failed (Random &, int vars);
  void generate_phase (Random &, int vars);
  void generate_conclude (Random &);
  void generate_freeze (Random &, int vars);
  void generate_melt (Random &);

  void generate_propagator (Random &, int minvars, int maxvars);
  void generate_lemmas (Random &);
  void generate_forces (Random &, int minvars, int maxvars);

  void generate_propagate (Random &);
  void generate_implied (Random &);

  void generate_limits (Random &);
};

/*------------------------------------------------------------------------*/

class Reader {

  Mobical &mobical;
  Trace &trace;

  const char *path;
  FILE *file;
  int lineno;
  bool close;
  int peeked = EOF;

  int next () {
    if (peeked != EOF) {
      int result = peeked;
      peeked = EOF;
      return result;
    }
    return getc (file);
  }
  int peek () {
    peeked = getc (file);
    return peeked;
  }

  [[noreturn]] void error (const char *fmt, ...);

public:
  Reader (Mobical &m, Trace &t, const char *p)
      : mobical (m), trace (t), lineno (1) {
    assert (p);
    if (!strcmp (p, "-"))
      path = "<stdin>", file = stdin, close = false;
    else if (!(file = fopen (p, "r")))
      mobical.die ("can not read '%s'", p);
    else
      path = p, close = true;
  }

  ~Reader () {
    if (close)
      fclose (file);
  }

  void parse ();
};

/*------------------------------------------------------------------------*/

size_t Trace::first_option () {
  size_t res;
  for (res = 0; res < size (); res++)
    if (calls[res]->type == Call::SET)
      return res;
  return res;
}

size_t Trace::last_option () {
  size_t res;
  for (res = 0; res < size (); res++) {
    Call *c = calls[res];
    if (c->type == Call::INIT)
      continue;
    if (c->type == Call::SET)
      continue;
    break;
  }
  return res;
}

Call *Trace::find_option_by_prefix (const char *name) {
  size_t last = last_option ();
  Call *res = 0;
  for (size_t i = first_option (); i < last; i++) {
    Call *c = calls[i];
    if (res && strlen (res->name) < strlen (c->name))
      continue;
    if (has_prefix (name, c->name))
      res = c;
  }
  return res;
}

Call *Trace::find_option_by_name (const char *name) {
  size_t last = last_option ();
  Call *res = 0;
  for (size_t i = first_option (); i < last; i++) {
    Call *c = calls[i];
    if (!strcmp (c->name, name))
      res = c;
  }
  return res;
}

// Some options are never part of generated traces.
//
bool Trace::ignored_option (const char *name) {
  if (!strcmp (name, "checkfrozen"))
    return true;
  if (!strcmp (name, "terminateint"))
    return true;
  return false;
}

// Check whether the trace already contains an option which disables the
// option 'name'.  Here we assume that an option disables another one if
// the disabling one has as name proper prefix of the disabled one and the
// value of the former is set to zero in the trace.
//
bool Trace::ignore_option (const char *name, int max_var) {

  if (ignored_option (name))
    return true;

  // There are options which should be kept at their default value unless
  // the formula is really small.  Otherwise the solver might run
  // 'forever'.
  //
  if (max_var > SMALL) {
    if (!strcmp (name, "reduce"))
      return true;
  }

  const Call *c = find_option_by_prefix (name);
  assert (!c || has_prefix (name, c->name));
  if (c && strlen (c->name) < strlen (name) && !c->val)
    return true;

  return false;
}

// For incomplete solving phases such as 'walk' we do not want to increase
// the option value above the default and similarly for elimination
// bounds.
//
int64_t Trace::option_high_value (const char *name, int64_t def, int64_t lo,
                                  int64_t hi) {
  assert (lo <= def), assert (def <= hi);
  if (!strcmp (name, "walkmaxeff"))
    return def;
  if (!strcmp (name, "walkmineff"))
    return def;
  if (!strcmp (name, "elimboundmax"))
    return 256;
  if (!strcmp (name, "elimboundmin"))
    return 256;
  (void) lo;
  return hi;
}

/*------------------------------------------------------------------------*/

void Trace::generate_options (Random &random, Size size) {

#ifdef LOGGING
  if (mobical.add_set_log_to_true)
    push_back (new SetCall ("log", 1));
#else
  if (mobical.add_set_log_to_true)
    mobical.warning ("ignoring log option");
#endif
  // In 10% of the cases do not change any options.
  //
  if (random.generate_double () < 0.1)
    return;

  // In order to increase throughput we enable 'walk' in 5% tests, which
  // means disabling it in 95% of the tests.
  //
  if (random.generate_double () < 0.95)
    push_back (new SetCall ("walk", 0));

  // Also for checking models and assumptions, but with 80% probability.
  //
  if (random.generate_double () < 0.8)
    push_back (new SetCall ("check", 1));

  // In 10% of the remaining cases we use a configuration.
  //
  if (random.generate_double () < 0.1) {
    const auto configs = Config::begin ();
    const int size = Config::end () - configs;
    const int pos = random.pick_int (0, size - 1);
    const char *config = configs[pos];
    assert (Config::has (config));
    push_back (new ConfigureCall (config));
  }

  // This is the fraction of options changed.
  //
  double fraction = random.generate_double ();

  // Generate a list of options, different from default values.
  //
  for (auto it = Options::begin (); it != Options::end (); it++) {
    const Option &o = *it;

    // This should not be reachable unless the low and high value of an
    // option in 'options.hpp' are the same.
    //
    if (o.lo == o.hi)
      continue;

    // We ignore logging here and set it below to make mobical
    // deterministic
    if (!strcmp (o.name, "log"))
      continue;
    if (!strcmp (o.name, "logsort"))
      continue;
    // We keep choosing the value for 'simplify' and 'walk' out of the
    // loop (see the arguments described above).
    //
    if (!strcmp (o.name, "simplify"))
      continue;
    if (!strcmp (o.name, "walk"))
      continue;

    // Probability to change an option is 'fraction'.
    //
    if (random.generate_double () < fraction)
      continue;

    // Unless we have to ignore it.
    //
    if (ignore_option (o.name, size))
      continue;

    int val;
    int64_t hi = option_high_value (o.name, o.def, o.lo, o.hi);
    if (o.lo < hi) {
      bool uniform = random.generate_double () < 0.05;
      if (uniform) {
        do
          val = random.pick_int (o.lo, hi);
        while (val == o.def);
      } else { // log uniform
        int64_t range = hi - (int64_t) o.lo;
        int log;
        assert (range <= INT_MAX);
        for (log = 0; log < 30 && (1 << log) < range; log++)
          if (random.generate_bool ())
            break;
        if ((1 << log) < range)
          range = (1l << log);
        val = o.lo + random.pick_int (0, range);
      }
    } else
      val = o.lo;
    push_back (new SetCall (o.name, val));
  }

  // Now setting the option for logging. Even if we do not generate the
  // log call, we need the side effect of generate_bool ()
  auto log_option =
      std::find_if (Options::begin (), Options::end (),
                    [] (const Option o) { return strcmp (o.name, "log"); });
  const bool should_log = random.generate_bool ();
  auto logsort_option = std::find_if (
      Options::begin (), Options::end (),
      [] (const Option o) { return strcmp (o.name, "logsort"); });
  const bool should_logsort = random.generate_bool ();

#ifdef LOGGING
  // sanity check
  assert (log_option != Options::end ());
  assert (logsort_option != Options::end ());
#endif
  if (log_option != Options::end () &&
      should_log) { // only if the option was found
#ifdef LOGGING
    push_back (new SetCall (log_option->name, should_log));
#endif
  }
  if (logsort_option != Options::end () && should_logsort) {
#ifdef LOGGING
    push_back (new SetCall (logsort_option->name, should_logsort));
#endif
  }
}

/*------------------------------------------------------------------------*/

void Trace::generate_queries (Random &random) {
  if (random.generate_double () < 0.02)
    push_back (new VarsCall ());
  if (random.generate_double () < 0.02)
    push_back (new ActiveCall ());
  if (random.generate_double () < 0.02)
    push_back (new RedundantCall ());
  if (random.generate_double () < 0.02)
    push_back (new IrredundantCall ());
}

/*------------------------------------------------------------------------*/

void Trace::generate_resize (Random &random, int max_var) {
  if (random.generate_double () > 0.01)
    return;
  int new_max_var = random.pick_int (0, 1.1 * max_var);
  push_back (new ResizeCall (new_max_var));
}

/*------------------------------------------------------------------------*/

void Trace::generate_declare_more_variables (Random &random) {
  if (random.generate_double () > 0.01)
    return;
  int new_max_var = random.pick_int (0, 100);
  push_back (new DeclareMoreVariablesCall (new_max_var));
}

void Trace::generate_declare_one_more_variable (Random &random) {
  if (random.generate_double () > 0.01)
    return;
  push_back (new DeclareOneMoreVariableCall ());
}

/*------------------------------------------------------------------------*/

void Trace::generate_implied (Random &random) {
  if (random.generate_double () > 0.01)
    return;
  push_back (new ImpliedCall ());
}

/*------------------------------------------------------------------------*/

void Trace::generate_propagate (Random &random) {
  if (random.generate_double () > 0.01)
    return;
  push_back (new PropagateImplyCall ());
}

/*------------------------------------------------------------------------*/

void Trace::generate_limits (Random &random) {
  if (random.generate_double () < 0.05)
    push_back (new LimitCall ("terminate", random.pick_log (0, 1e5)));
  if (random.generate_double () < 0.05)
    push_back (new LimitCall ("conflicts", random.pick_log (0, 1e4)));
  if (random.generate_double () < 0.05)
    push_back (new LimitCall ("decisions", random.pick_log (0, 1e4)));
  if (random.generate_double () < 0.05)
    push_back (new LimitCall ("ticks", random.pick_log (0, 1e9)));
  if (random.generate_double () < 0.1)
    push_back (new LimitCall ("preprocessing", random.pick_int (0, 10)));
  if (random.generate_double () < 0.05)
    push_back (new LimitCall ("localsearch", random.pick_int (0, 1)));
  if (random.generate_double () < 0.02)
    push_back (new OptimizeCall (random.pick_int (0, 31)));
}

/*------------------------------------------------------------------------*/

static int pick_size (Random &random, int vars) {
  int res;
  double prop = random.generate_double ();
  if (prop < 0.0001)
    res = 0;
  else if (prop < 0.001)
    res = 1;
  else if (prop < 0.01)
    res = 2;
  else if (prop < 0.90)
    res = 3;
  else if (prop < 0.95)
    res = 4;
  else
    res = random.pick_int (5, 20);
  if (res > vars)
    res = vars;
  return res;
}

static int pick_literal (Random &random, int minvars, int maxvars,
                         vector<int> &clause) {
  assert (minvars <= maxvars);
  int res = 0;
  while (!res) {
    int idx = random.pick_int (minvars, maxvars);
    double prop = random.generate_double ();
    if (prop > 0.001) {
      bool duplicated = false;
      for (size_t i = 0; !duplicated && i < clause.size (); i++)
        duplicated = (abs (clause[i]) == idx);
      if (duplicated)
        continue;
    }
    bool sign = random.generate_bool ();
    res = sign ? -idx : idx;
  }
  return res;
}

void Trace::generate_clause (Random &random, int minvars, int maxvars,
                             int uniform) {
  assert (minvars <= maxvars);
  int maxsize = maxvars - minvars + 1;
  int size = uniform ? uniform : pick_size (random, maxsize);
  vector<int> clause;
  for (int i = 0; i < size; i++) {
    int lit = pick_literal (random, minvars, maxvars, clause);
    push_back (new AddCall (lit));
    clause.push_back (lit);
  }
  push_back (new AddCall (0));
}

void Trace::generate_constraint (Random &random, int minvars, int maxvars,
                                 int uniform) {
  if (random.generate_double () < 0.95)
    return;
  assert (minvars <= maxvars);
  int maxsize = maxvars - minvars + 1;
  int size = uniform ? uniform : pick_size (random, maxsize);
  vector<int> clause;
  for (int i = 0; i < size; i++) {
    int lit = pick_literal (random, minvars, maxvars, clause);
    push_back (new ConstrainCall (lit));
    clause.push_back (lit);
  }
  push_back (new ConstrainCall (0));
  if (random.generate_double () < 0.01)
    return;
  // Generating a new constraint deletes the old one.
  clause.clear ();
  for (int i = 0; i < size; i++) {
    int lit = pick_literal (random, minvars, maxvars, clause);
    push_back (new ConstrainCall (lit));
    clause.push_back (lit);
  }
  push_back (new ConstrainCall (0));
}

/*------------------------------------------------------------------------*/
void Trace::generate_propagator (Random &random, int minvars, int maxvars) {
  // No Propagator in 90% of cases.
  if (!in_connection && random.generate_double () < 0.9) {
    return;
  }
  if (!in_connection) {
    push_back (new ConnectCall ());
    in_connection = true;
  } else if (random.generate_double () < 0.1) {
    observed_vars.clear ();
    push_back (new DisconnectCall ());
    in_connection = false;
    return;
  } else if (random.generate_double () < 0.05) {
    observed_vars.clear ();
    push_back (new DisconnectCall ());
    push_back (new ConnectCall ());
  } else if (random.generate_double () < 0.25) {
    auto p = observed_vars.begin ();
    auto q = p;
    const auto end = observed_vars.end ();
    while (p != end) {
      int var = *q++ = *p++;
      if (random.generate_double () < 0.1) {
        q--;
        push_back (new UnObserveCall (var));
      }
    }
    observed_vars.resize (q - observed_vars.begin ());
  } else if (random.generate_double () < 0.05) {
    push_back (new ResetObservedCall ());
  }

  assert (in_connection);
  assert (minvars <= maxvars);

  const int diff = maxvars - minvars;

  // Give a chance to add no observed variables at all
  if (random.generate_double () < 0.03)
    return;

  for (int idx = minvars; idx <= maxvars; idx++) {
    if (random.generate_double () < 0.4)
      continue;
    if (std::find (observed_vars.begin (), observed_vars.end (), idx) !=
        observed_vars.end ())
      continue;
    int lit = random.generate_bool () ? -idx : idx;
    push_back (new ObserveCall (lit));
    observed_vars.push_back (abs (lit));
  }
  for (int idx = maxvars + 1; idx <= maxvars + 2 * diff; idx++) {
    if (random.generate_double () < 0.8)
      continue;
    if (std::find (observed_vars.begin (), observed_vars.end (), idx) !=
        observed_vars.end ())
      continue;
    int lit = random.generate_bool () ? -idx : idx;
    push_back (new ObserveCall (lit));
    observed_vars.push_back (abs (lit));
  }
}

void Trace::generate_forces (Random &random, int minvars, int maxvars) {
  if (!in_connection)
    return;

  assert (minvars <= maxvars);

  const int diff = maxvars - minvars;

  // Give a chance to add no forces.
  if (random.generate_double () < 0.1)
    return;

  // TODO: MockForceType length.
  for (int i = 0; i < LAST_MOCK_FORCE_TYPE; i++) {
    // chance to not generate this type.
    if (random.generate_double () < 0.1)
      continue;
    const MockForceType type = static_cast<MockForceType> (i);
    for (int j = 0; j < diff; j++) {
      if (random.generate_double () < 0.1)
        break;
      const int idx = random.pick_int (minvars, maxvars);
      const int lit = random.generate_bool () ? -idx : idx;
      const int delay = random.pick_int (0, 50);
      push_back (new MockForceCall (lit, type, delay));
    }
  }
}

void Trace::generate_lemmas (Random &random) {
  if (!in_connection)
    return;

  // TODO: also generate lemmas with unobserved variables
  if (!observed_vars.size ())
    return;

  const int ovars = observed_vars.size ();

  if (random.generate_double () >= 0.05) {
    const int nof_decide = random.pick_int (50, 170);
    for (int i = 0; i < nof_decide; i++) {
      const int max_idx = ovars - 1;
      int idx = random.pick_int (0, max_idx);
      int lit = random.generate_bool () ? -observed_vars[idx]
                                        : observed_vars[idx];
      int delay = random.pick_int (0, 50);
      push_back (new DecideCall (lit, delay));
    }
  }
  if (random.generate_double () >= 0.05) {
    const int nof_lemmas = random.pick_int (30, 175);
    for (int i = 0; i < nof_lemmas; i++) {
      // TODO:sizeof LemmaType
      LemmaType lemmatype = EAGER;
      if (random.generate_double () < 0.1)
        lemmatype = LAZY;
      if (random.generate_double () < 0.2)
        lemmatype = OBSERVING;
      if (random.generate_double () < 0.6)
        lemmatype = PROPAGATING;
      int delay = random.pick_int (0, 50);

      int count = pick_size (random, ovars);
      const int max_idx = ovars - 1;
      bool *picked = new bool[max_idx + 1];
      for (int i = 0; i <= max_idx; i++)
        picked[i] = false;
      for (int i = 0; i < count; i++) {
        int idx;
        do
          idx = random.pick_int (0, max_idx);
        while (picked[idx]);
        picked[idx] = 1;
        int lit = random.generate_bool () ? -observed_vars[idx]
                                          : observed_vars[idx];
        push_back (new LemmaCall (lit, lemmatype, 0));
      }

      delete[] picked;
      if (random.generate_double () < 0.1) {
        int idx = random.pick_int (0, max_idx);
        int lit = random.generate_bool () ? -observed_vars[idx]
                                          : observed_vars[idx];
        push_back (new LemmaCall (lit, lemmatype, 0));
      }
      push_back (new LemmaCall (0, lemmatype, delay));
    }
  }
}

/*------------------------------------------------------------------------*/

void Trace::generate_assume (Random &random, int vars) {
  if (random.generate_double () < 0.15)
    return;
  int count;
  if (random.generate_bool ())
    count = 1;
  else
    count = random.pick_int (1, vars + 1);
  const int max_vars = vars + 2;
  bool *picked = new bool[max_vars + 1];
  for (int i = 1; i <= max_vars; i++)
    picked[i] = false;
  for (int i = 0; i < count; i++) {
    int idx;
    do
      idx = random.pick_int (1, max_vars);
    while (picked[idx]);
    picked[idx] = 1;
    int lit = random.generate_bool () ? -idx : idx;
    push_back (new AssumeCall (lit));
  }
  if (random.generate_double () < 0.01)
    push_back (new ResetAssumptionsCall ());
  delete[] picked;
  if (random.generate_double () < 0.1) {
    int idx = random.pick_int (1, max_vars);
    int lit = random.generate_bool () ? -idx : idx;
    push_back (new AssumeCall (lit));
  }
}

void Trace::generate_values (Random &random, int vars) {
  if (random.generate_double () < 0.1)
    return;
  double fraction = random.generate_double ();
  for (int idx = 1; idx <= vars; idx++) {
    if (fraction < random.generate_double ())
      continue;
    int lit = random.generate_bool () ? -idx : idx;
    bool strict = random.generate_bool ();
    push_back (new ValCall (lit, strict));
  }
  if (random.generate_double () < 0.1) {
    int idx = random.pick_int (vars + 1, vars * 1.5 + 1);
    int lit = random.generate_bool () ? -idx : idx;
    push_back (new ValCall (lit, true));
  }
}

void Trace::generate_flipped (Random &random, int vars) {
  if (random.generate_double () < 0.5)
    return;
  double fraction = random.generate_double ();
  for (int idx = 1; idx <= vars; idx++) {
    if (fraction < random.generate_double ())
      continue;
    int lit = random.generate_bool () ? -idx : idx;
    if (random.generate_double () < 0.5)
      push_back (new FlippableCall (lit));
    else
      push_back (new FlipCall (lit));
  }
  if (random.generate_double () < 0.1) {
    int idx = random.pick_int (vars + 1, vars * 1.5 + 1);
    int lit = random.generate_bool () ? -idx : idx;
    if (random.generate_double () < 0.5)
      push_back (new FlippableCall (lit));
    else
      push_back (new FlipCall (lit));
  }
}

void Trace::generate_failed (Random &random, int vars) {
  if (random.generate_double () < 0.05)
    return;
  double fraction = random.generate_double ();
  for (int idx = 1; idx <= vars; idx++) {
    if (fraction < random.generate_double ())
      continue;
    int lit = random.generate_bool () ? -idx : idx;
    push_back (new FailedCall (lit));
  }
  if (random.generate_double () < 0.05) {
    int idx = random.pick_int (vars + 1, vars * 1.5 + 1);
    int lit = random.generate_bool () ? -idx : idx;
    push_back (new FailedCall (lit));
  }
}

void Trace::generate_conclude (Random &random) {
  if (random.generate_double () < 0.95)
    return;
  push_back (new ConcludeCall ());
}

void Trace::generate_frozen (Random &random, int vars) {
  if (random.generate_double () < 0.05)
    return;
  double fraction = random.generate_double ();
  for (int idx = 1; idx <= vars; idx++) {
    if (fraction < random.generate_double ())
      continue;
    int lit = random.generate_bool () ? -idx : idx;
    push_back (new FrozenCall (lit));
  }
  if (random.generate_double () < 0.05) {
    int idx = random.pick_int (vars + 1, vars * 1.5 + 1);
    int lit = random.generate_bool () ? -idx : idx;
    push_back (new FrozenCall (lit));
  }
}

void Trace::generate_phase (Random &random, int vars) {
  if (random.generate_double () < 0.05)
    return;
  double fraction = random.generate_double ();
  for (int idx = 1; idx <= vars; idx++) {
    if (fraction < random.generate_double ())
      continue;
    int lit = random.generate_bool () ? -idx : idx;
    bool unphase = random.generate_double () < 0.05;
    if (unphase)
      push_back (new UnPhaseCall (lit));
    else
      push_back (new PhaseCall (lit));
  }
  if (random.generate_double () < 0.05) {
    int idx = random.pick_int (vars + 1, vars * 1.5 + 1);
    int lit = random.generate_bool () ? -idx : idx;
    bool unphase = random.generate_double () < 0.05;
    if (unphase)
      push_back (new UnPhaseCall (lit));
    else
      push_back (new PhaseCall (lit));
  }
}

void Trace::generate_melt (Random &random) {
  if (random.generate_bool ())
    return;
  int m = vars ();
  int64_t *frozen = new int64_t[m + 1];
  for (int i = 1; i <= m; i++)
    frozen[i] = 0;
  for (size_t i = 0; i < size (); i++) {
    Call *c = calls[i];
    if (c->type == Call::MELT) {
      int idx = abs (c->arg);
      assert (idx > 0), assert (idx <= m);
      assert (frozen[idx] > 0);
      frozen[idx]--;
    } else if (c->type == Call::FREEZE) {
      int idx = abs (c->arg);
      assert (idx > 0), assert (idx <= m);
      frozen[idx]++;
    }
  }
  vector<int> candidates;
  for (int i = 1; i <= m; i++)
    if (frozen[i])
      candidates.push_back (i);
  delete[] frozen;
  double fraction = random.generate_double () * 0.4;
  for (auto idx : candidates) {
    if (random.generate_double () <= fraction)
      continue;
    int lit = random.generate_bool () ? -idx : idx;
    push_back (new MeltCall (lit));
  }
}

void Trace::generate_freeze (Random &random, int vars) {
  if (random.generate_bool ())
    return;
  double fraction = random.generate_double () * 0.5;
  for (int idx = 1; idx <= vars; idx++) {
    if (random.generate_double () <= fraction)
      continue;
    int lit = random.generate_bool () ? -idx : idx;
    push_back (new FreezeCall (lit));
  }
}

void Trace::generate_process (Random &random) {
  if (mobical.add_dump_before_solve)
    push_back (new DumpCall ());

  const double fraction = random.generate_double ();

  if (fraction < 0.6) {
    push_back (new SolveCall ());
  } else if (fraction > 0.99) {
    const int depth = random.pick_int (0, 10);
    push_back (new CubingCall (depth));
  } else if (fraction > 0.9) {
    push_back (new LookaheadCall ());
  } else if (fraction > 0.85) {
    push_back (new PropagateAssumptionsCall ());
  } else {
    const int rounds = random.pick_int (0, 10);
    push_back (new SimplifyCall (rounds));
  }

  if (mobical.add_stats_after_solve)
    push_back (new StatsCall ());
}

void Trace::generate (uint64_t i, uint64_t s) {

  id = i;
  seed = s;
  Random random (seed);

  // avoid different traces with MEMORY or TERMINATE
  int mallocall = random.pick_int (0, 2);
  int mallocallsize = random.pick_log (1e2, 1e6);
  int leakallocall = random.pick_int (0, 2);
  int terminatecall = random.pick_int (0, 2);
  int terminatecallsize = random.pick_log (1e1, 1e4);
#ifdef MOBICAL_MEMORY
  if (mobical.bad_alloc && (mallocall == 0))
    push_back (new MaxAllocCall (mallocallsize));
  if (mobical.leak_alloc && (leakallocall == 0))
    push_back (new LeakAllocCall ());
#else
  (void) mallocall;
  (void) mallocallsize;
  (void) leakallocall;
#endif
#ifdef MOBICAL_TERMINATE
  if (mobical.terminator && (terminatecall == 0))
    push_back (new TerminateCall (terminatecallsize));
#else
  (void) terminatecall;
  (void) terminatecallsize;
#endif

  push_back (new InitCall ());

  Size size;

  if (mobical.force.size)
    size = mobical.force.size;
  else {
    switch (random.pick_int (1, 3)) {
    case 1:
      size = SMALL;
      break;
    case 2:
      size = MEDIUM;
      break;
    default:
      size = BIG;
      break;
    }
  }

  generate_options (random, size);

  if (mobical.add_plain_after_options)
    push_back (new ConfigureCall ("plain"));

  int calls;
  if (mobical.force.phases < 0)
    calls = random.pick_int (1, 4);
  else
    calls = mobical.force.phases;

  int minvars, maxvars = 0;

  for (int call = 0; call < calls; call++) {
    int range;
    double ratio;
    int uniform;

    if (size == TINY)
      range = random.pick_int (1, TINY);
    else if (size == SMALL)
      range = random.pick_int (1, SMALL);
    else if (size == MEDIUM)
      range = random.pick_int (SMALL + 1, MEDIUM);
    else
      range = random.pick_int (MEDIUM + 1, BIG);

    if (random.generate_bool ())
      uniform = 0;
    else if (size == TINY)
      uniform = 0;
    else if (size == SMALL)
      uniform = random.pick_int (3, 7);
    else if (size == MEDIUM)
      uniform = random.pick_int (3, 4);
    else
      uniform = random.pick_int (3, 3);

    switch (uniform) {
    default:
      ratio = 4.267;
      break;
    case 4:
      ratio = 9.931;
      break;
    case 5:
      ratio = 21.117;
      break;
    case 6:
      ratio = 43.37;
      break;
    case 7:
      ratio = 87.79;
      break;
    }

    int clauses = range * ratio;

    // TODO: Test empty clause database by uncommenting here
    // Note that it can lead to unvalid mobical states in the reduced
    // trace, so always check the original bug-trace too.
    // if (random.generate_double () < 0.01) clauses = 0;

    minvars = random.pick_int (1, maxvars + 1);
    maxvars = minvars + range;

    for (int j = 0; j < clauses; j++)
      generate_queries (random), generate_resize (random, maxvars),
          generate_declare_more_variables (random),
          generate_declare_one_more_variable (random),
          generate_implied (random), generate_propagate (random),
          generate_clause (random, minvars, maxvars, uniform);

    generate_propagator (random, minvars, maxvars);

    generate_constraint (random, minvars, maxvars, uniform);
    generate_assume (random, maxvars);
    generate_melt (random);
    generate_freeze (random, maxvars);
    generate_limits (random);
    generate_phase (random, maxvars);

    generate_process (random);
    generate_lemmas (random);
    generate_forces (random, minvars, maxvars);

    generate_values (random, maxvars);
    if (!in_connection)
      generate_flipped (random, maxvars);
    generate_failed (random, maxvars);
    generate_conclude (random);
    generate_frozen (random, maxvars);
  }

  push_back (new ResetCall ());
}

/*------------------------------------------------------------------------*/

void Mobical::hline () {
  prefix ();
  terminal.normal ();
  cerr << setfill ('-') << setw (76) << "" << setfill (' ') << endl;
  terminal.normal ();
}

void Mobical::empty_line () { cerr << prefix_string () << endl; }

static int rounded_percent (double a, double b) {
  return 0.5 + percent (a, b);
}

void Mobical::add_statistics (Solver *solver) {
  assert (solver);
  assert (shared);
#define STATISTIC(NAME, VERBOSE, REF, SYMBOL, PRINT) \
  shared->stats_sum.NAME += solver->internal->stats.NAME;
#ifndef NMETRICS
#define METRIC(NAME, VERBOSE, REF, SYMBOL, PRINT) \
  STATISTIC (NAME, VERBOSE, REF, SYMBOL, PRINT)
#else
#define METRIC(NAME, VERBOSE, REF, SYMBOL, PRINT)
#endif

  CADICAL_STATISTICS

#undef STATISTIC
#undef METRIC

#define STATISTIC(NAME, VERBOSE, REF, SYMBOL, PRINT) \
  if (solver->internal->stats.NAME) \
    shared->stats_count.NAME++;
#ifndef NMETRICS
#define METRIC(NAME, VERBOSE, REF, SYMBOL, PRINT) \
  STATISTIC (NAME, VERBOSE, REF, SYMBOL, PRINT)
#else
#define METRIC(NAME, VERBOSE, REF, SYMBOL, PRINT)
#endif
  CADICAL_STATISTICS

#undef STATISTIC
#undef METRIC
}

#define PRINT_STATER(NAME, PRIMARY, INC, SECONDARY) \
  do { \
    const int RELATIVE = percent (INC, SECONDARY); \
    const size_t PNUMBER = std::to_string (PRIMARY).length (); \
    const size_t OFFSET1 = 55 - strlen (NAME) - PNUMBER; \
    const size_t SNUMBER = std::to_string (INC).length (); \
    const size_t OFFSET2 = 10 - SNUMBER; \
    const size_t RNUMBER = std::to_string (RELATIVE).length (); \
    const size_t OFFSET3 = 4 - RNUMBER; \
    prefix (); \
    terminal.normal (); \
    cerr << NAME << ":"; \
    cerr << setfill (' ') << setw (OFFSET1) << " "; \
    cerr << PRIMARY << " "; \
    cerr << setfill (' ') << setw (OFFSET2) << " "; \
    cerr << INC << " "; \
    cerr << setfill (' ') << setw (OFFSET3) << " "; \
    terminal.bold (); \
    if (RELATIVE < 20) \
      terminal.red (true); \
    else if (RELATIVE > 80) \
      terminal.green (true); \
    else \
      terminal.yellow (true); \
    cerr << RELATIVE << " %" << std::endl; \
    terminal.normal (); \
  } while (0)

void Mobical::section (const char *title) {
  prefix ();
  cerr << endl;
  prefix ();
  tout.blue ();
  fputs ("--- [ ", stderr);
  tout.blue (true);
  fputs (title, stderr);
  tout.blue ();
  fputs (" ] ", stderr);
  for (int i = strlen (title) + 11; i < 78; i++)
    fputc ('-', stderr);
  tout.normal ();
  fputc ('\n', stderr);
  fflush (stderr);
  prefix ();
  cerr << endl;
}

void Mobical::print_statistics () {

  if (!quiet)
    hline ();

  if (!mobical.donot.summary && mobical.shared) {
    section ("summary");
#define STATISTIC(NAME, VERBOSE, COMMAND, OTHER, SYMBOL) \
  PRINT_STATER (#NAME, shared->stats_sum.NAME, shared->stats_count.NAME, \
                shared->executed);
#ifndef NMETRICS
#define METRIC(NAME, VERBOSE, COMMAND, OTHER, SYMBOL) \
  PRINT_STATER (#NAME, (int64_t) shared->stats_sum.NAME, \
                (int64_t) shared->stats_count.NAME, shared->executed);
#else
#define METRIC(NAME, VERBOSE, COMMAND, OTHER, SYMBOL)
#endif
    CADICAL_STATISTICS

#undef STATISTIC
#undef METRIC

    section ("total");
  }

  prefix ();
  cerr << "generated " << Trace::generated << " traces: ";
  if (Trace::ok > 0)
    terminal.green (true);
  cerr << Trace::ok << " ok "
       << rounded_percent (Trace::ok, Trace::generated) << "%";
  if (Trace::ok > 0)
    terminal.normal ();
  cerr << ", ";
  if (Trace::failed > 0)
    terminal.red (true);
  cerr << Trace::failed << " failed "
       << rounded_percent (Trace::failed, Trace::generated) << "%";
  if (Trace::failed > 0)
    terminal.normal ();
  cerr << ", " << Trace::executed << " executed" << endl << flush;

  if (shared) {
    prefix ();
    cerr << "solved " << shared->solved << ": " << terr.blue_code ()
         << shared->sat << " sat "
         << rounded_percent (shared->sat, shared->solved) << "%"
         << terr.normal_code () << ", " << terr.magenta_code ()
         << shared->unsat << " unsat "
         << rounded_percent (shared->unsat, shared->solved) << "%"
         << terr.normal_code () << ", " << shared->incremental
         << " incremental "
         << rounded_percent (shared->incremental, shared->solved) << "%"
         << terr.normal_code () << ", " << terr.yellow_code ()
         << shared->oom << " oom "
         << rounded_percent (shared->oom, shared->solved) << "%" << endl
         << flush;
    if (shared->memout || shared->timeout) {
      prefix ();
      cerr << "out-of-time " << shared->timeout << ", "
           << "out-of-memory " << shared->memout << endl
           << flush;
    }
  }

  if (spurious) {
    prefix ();
    cerr << "generated " << spurious << " spurious traces "
         << rounded_percent (spurious, traces) << "%" << endl
         << flush;
  }
}

/*------------------------------------------------------------------------*/

extern "C" {
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
}

#ifndef _WIN32

extern "C" {
#include <sys/resource.h>
#include <sys/wait.h>
}

#endif

int64_t Trace::generated = 0;
int64_t Trace::executed = 0;
int64_t Trace::failed = 0;
int64_t Trace::ok = 0;

int64_t Trace::trace_call_index = -1;
#ifdef MOBICAL_MEMORY
int64_t Trace::memory_bad_alloc = 0;
int64_t Trace::memory_bad_size = 0;
int64_t Trace::memory_bad_failed = 0;
int64_t Trace::memory_leak_alloc = 0;
int64_t Trace::memory_leak_next_free = 0;
#endif
#ifdef MOBICAL_TERMINATE
int64_t Trace::limit_terminate = 0;
int64_t Trace::limit_terminate_remaining = 0;
#endif

#define SIGNAL(SIG) void (*Trace::old_##SIG##_handler) (int);
SIGNALS
#undef SIGNAL

void Trace::reset_child_signal_handlers () {
#define SIGNAL(SIG) signal (SIG, old_##SIG##_handler);
  SIGNALS
#undef SIGNAL
}

void Trace::child_signal_handler (int sig) {
#ifdef MOBICAL_MEMORY
  hooks_uninstall ();
  if (memory_bad_failed) {
    mobical.shared->bad_alloc.signal_call_index = trace_call_index;
    mobical.shared->bad_alloc.signal_stack_size =
        backtrace (mobical.shared->bad_alloc.signal_stack_array,
                   MOBICAL_MEMORY_STACK_COUNT);
    // The signal probably has been raised as a result
    // of the forced failed memory allocation.
    // Raise a custom signal code for the parent to
    // create a unique result code.
    reset_child_signal_handlers ();
    raise (SIGUSR1);
  }
#endif
#ifdef MOBICAL_TERMINATE
  if (limit_terminate && !limit_terminate_remaining) {
    mobical.shared->limit_terminate.signal_call_index = trace_call_index;
    mobical.shared->limit_terminate.signal_stack_size =
        backtrace (mobical.shared->limit_terminate.signal_stack_array,
                   MOBICAL_TERMINATE_STACK_COUNT);
    // The signal probably has been raised as a result
    // of the termination request and an assertion failing.
    // Raise a custom signal code for the parent to
    // create a unique result code.
    reset_child_signal_handlers ();
    raise (SIGTSTP);
  }
#endif

  struct rusage u;
  if (!getrusage (RUSAGE_SELF, &u)) {
    if ((int64_t) u.ru_maxrss >> 10 >= mobical.space_limit) {
      if (mobical.shared)
        mobical.shared->memout++;
      // Since there is no memout signal we just misuse SIXCPU to notify
      // the calling process that this is a out-of-resource situation.
      sig = SIGXCPU;
    } else {
      double t = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec +
                 u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
      if (t >= mobical.time_limit) {
        if (mobical.shared)
          mobical.shared->timeout++;
        sig = SIGXCPU;
      }
    }
  }
  reset_child_signal_handlers ();
  raise (sig);
}

void Trace::init_child_signal_handlers () {
#define SIGNAL(SIG) \
  old_##SIG##_handler = signal (SIG, child_signal_handler);
  SIGNALS
#undef SIGNAL
}

#ifdef MOBICAL_MEMORY
void Trace::hooks_install (void) {
  *static_cast<volatile malloc_t *> (&::hook_malloc) = &hook_malloc;
  *static_cast<volatile realloc_t *> (&::hook_realloc) = &hook_realloc;
  *static_cast<volatile free_t *> (&::hook_free) = &hook_free;
}

void Trace::hooks_uninstall (void) {
  *static_cast<volatile malloc_t *> (&::hook_malloc) = nullptr;
  *static_cast<volatile realloc_t *> (&::hook_realloc) = nullptr;
  *static_cast<volatile free_t *> (&::hook_free) = nullptr;
}

void *Trace::hook_malloc (size_t size) {
  // Failing allocator
  if (memory_bad_alloc > 0) {
    memory_bad_size += size + 1; // + 1 to catch allocations of size 0
    if (memory_bad_size > memory_bad_alloc && !memory_bad_failed) {
      memory_bad_failed = 1;
      hooks_uninstall ();
      mobical.shared->bad_alloc.alloc_call_index = trace_call_index;
      mobical.shared->bad_alloc.alloc_stack_size =
          backtrace (mobical.shared->bad_alloc.alloc_stack_array,
                     MOBICAL_MEMORY_STACK_COUNT);
      hooks_install ();
      return nullptr;
    }
  }
  // Default allocator
  void *ptr = (*libc_malloc) (size);

  // Leak detection
  if (memory_leak_alloc > 0) {
    for (size_t offset{0u}; offset < MOBICAL_MEMORY_LEAK_COUNT; offset++) {
      size_t index{memory_leak_next_free + offset};
      if (index >= MOBICAL_MEMORY_LEAK_COUNT)
        index -= MOBICAL_MEMORY_LEAK_COUNT;
      if (mobical.shared->leak_alloc.alloc_ptr[index] != nullptr) {
        continue;
      }
      // Found free slot
      hooks_uninstall ();
      mobical.shared->leak_alloc.alloc_size[index] = size;
      mobical.shared->leak_alloc.alloc_ptr[index] = ptr;
      mobical.shared->leak_alloc.call_index[index] = trace_call_index;
      mobical.shared->leak_alloc.stack_size[index] =
          backtrace (mobical.shared->leak_alloc.stack_array[index],
                     MOBICAL_MEMORY_STACK_COUNT);
      memory_leak_next_free = index + 1;
      hooks_install ();
      return ptr;
    }
  }
  return ptr;
}

void *Trace::hook_realloc (void *ptr, size_t size) {
  // Failing allocator
  if (memory_bad_alloc > 0) {
    memory_bad_size += size + 1; // + 1 to catch allocations of size 0
    if (memory_bad_size > memory_bad_alloc && !memory_bad_failed) {
      hooks_uninstall ();
      memory_bad_failed = 1;
      mobical.shared->bad_alloc.alloc_call_index = trace_call_index;
      mobical.shared->bad_alloc.alloc_stack_size =
          backtrace (mobical.shared->bad_alloc.alloc_stack_array,
                     MOBICAL_MEMORY_STACK_COUNT);
      hooks_install ();
      return nullptr;
    }
  }
  // Default allocator
  void *new_ptr = (*libc_realloc) (ptr, size);
  // Leak detection
  if (memory_leak_alloc > 0) {
    for (size_t index{0u}; index < MOBICAL_MEMORY_LEAK_COUNT; index++) {
      if (mobical.shared->leak_alloc.alloc_ptr[index] != ptr) {
        continue;
      }
      // Found previous slot
      hooks_uninstall ();
      mobical.shared->leak_alloc.alloc_size[index] = size;
      mobical.shared->leak_alloc.alloc_ptr[index] = new_ptr;
      mobical.shared->leak_alloc.call_index[index] = trace_call_index;
      mobical.shared->leak_alloc.stack_size[index] =
          backtrace (mobical.shared->leak_alloc.stack_array[index],
                     MOBICAL_MEMORY_STACK_COUNT);
      hooks_install ();
      return new_ptr;
    }
    for (size_t offset{0u}; offset < MOBICAL_MEMORY_LEAK_COUNT; offset++) {
      size_t index{memory_leak_next_free + offset};
      if (index >= MOBICAL_MEMORY_LEAK_COUNT)
        index -= MOBICAL_MEMORY_LEAK_COUNT;
      if (mobical.shared->leak_alloc.alloc_ptr[index] != nullptr) {
        continue;
      }
      // Found free slot
      hooks_uninstall ();
      mobical.shared->leak_alloc.alloc_size[index] = size;
      mobical.shared->leak_alloc.alloc_ptr[index] = new_ptr;
      mobical.shared->leak_alloc.call_index[index] = trace_call_index;
      mobical.shared->leak_alloc.stack_size[index] =
          backtrace (mobical.shared->leak_alloc.stack_array[index],
                     MOBICAL_MEMORY_STACK_COUNT);
      memory_leak_next_free = index + 1;
      hooks_install ();
      return new_ptr;
    }

    hooks_uninstall ();
    mobical.warning ("No free slot!");
    hooks_install ();
  }
  return new_ptr;
}

void Trace::hook_free (void *ptr) {
  (*libc_free) (ptr);
  // Leak detection
  if (memory_leak_alloc > 0) {
    for (size_t index{0u}; index < MOBICAL_MEMORY_LEAK_COUNT; index++) {
      if (mobical.shared->leak_alloc.alloc_ptr[index] == ptr) {
        mobical.shared->leak_alloc.alloc_size[index] = 0;
        mobical.shared->leak_alloc.alloc_ptr[index] = nullptr;
        mobical.shared->leak_alloc.call_index[index] = 0;
        mobical.shared->leak_alloc.stack_size[index] = 0;
        // memory_leak_next_free = index;
        break;
      }
    }
  }
}
#endif

#ifdef MOBICAL_PRINT_TRACE
void Trace::print_trace (void **stack_array, size_t stack_size, ostream &os,
                         size_t start_index) {
  char **stack_text = backtrace_symbols (stack_array, stack_size);
  for (size_t stack_index = start_index; stack_index < stack_size;
       stack_index++) {
    string stack_entry = stack_text[stack_index];
    size_t position = stack_entry.rfind ("/");
    if (position != string::npos) {
      stack_entry = stack_entry.substr (position + 1);
    }
    smatch match; // Try to unmangle C++ method names
    regex regex_function_name (
        "^(.*?)\\(([a-zA-Z0-9_]+)((?:\\+0x[0-9a-fA-F]+)?)\\)(.*?)");
    if (regex_match (stack_entry, match, regex_function_name)) {
      string mangledName = match[2];
      int status = -1;
      char *demangledName =
          abi::__cxa_demangle (mangledName.c_str (), NULL, NULL, &status);
      if (status == 0) { // Print C++ method name
        os << "# " << match[1] << "(" << demangledName << match[3] << ")"
           << match[4] << endl;
        free (static_cast<void *> (demangledName));
      } else { // Print C method name
        os << "# " << match[1] << "(" << mangledName << match[3] << ")"
           << match[4] << endl;
      }
    } else { // Print unparsable stack entry
      os << "# " << stack_entry << endl;
    }
  }
  free (static_cast<void *> (stack_text));
}
#endif

int Trace::fork_and_execute () {

  cerr << flush;
  pid_t child = mobical.donot.fork ? 0 : fork ();
  int res = 0;

  if (child) {

    executed++;

    // disable core dumps for faster delta-debugging.
#ifndef _WIN32
#ifdef __APPLE__
    rlimit limit;
    limit.rlim_cur = 0;
    limit.rlim_max = 0;
    setrlimit (RLIMIT_CORE, &limit);
#else
    rlimit64 limit;
    limit.rlim_cur = 0;
    limit.rlim_max = 0;
    setrlimit64 (RLIMIT_CORE, &limit);
#endif
#endif

    int status, other = wait (&status);
    if (other != child)
      res = 0;
    else if (WIFEXITED (status))
      res = WEXITSTATUS (status);
    else if (!WIFSIGNALED (status))
      res = 0;
    else if (WTERMSIG (status) == SIGABRT)
      res = 1;
    else if (WTERMSIG (status) == SIGXCPU) {
      // Memout (space_limit) or timeout (time_limit)
      res = mobical.donot.ignore_resource_limits ? 2 : 0;
    } else if (WTERMSIG (status) == SIGUSR1)
      res = 3; // Bad allocation caused signal.
    else if (WTERMSIG (status) == SIGUSR2)
      res = 4; // Leaked allocation caused signal.
    else if (WTERMSIG (status) == SIGTSTP)
      res = 5; // Termination caused signal.
    else
      res = 6;

  } else {

    if (!mobical.donot.fork && mobical.time_limit) {
      struct rlimit rlim;
      if (!getrlimit (RLIMIT_CPU, &rlim)) {
        rlim.rlim_cur = mobical.time_limit;
        setrlimit (RLIMIT_CPU, &rlim);
      }
    }

    if (!mobical.donot.fork && mobical.space_limit) {
      struct rlimit rlim;
      if (!getrlimit (RLIMIT_AS, &rlim)) {
        rlim.rlim_cur = mobical.space_limit * (1l << 20);
        setrlimit (RLIMIT_AS, &rlim);
      }
    }

    init_child_signal_handlers ();
    dup2 (1, 3);
    dup2 (2, 4);
    int null = open ("/dev/null", O_WRONLY);
    assert (null);
    dup2 (null, 1);
    dup2 (null, 2);
    execute ();
    close (1);
    close (2);
    close (null);
    dup2 (3, 1);
    dup2 (4, 2);
    close (3);
    close (4);
    if (mobical.donot.fork) {
      delete mobical.mock_pointer;
      mobical.mock_pointer = nullptr;
      delete mobical.replay_pointer;
      mobical.replay_pointer = nullptr;
    }
    reset_child_signal_handlers ();

    if (!mobical.donot.fork)
      exit (0);
  }

  return res;
}

/*------------------------------------------------------------------------*/

// Delta-debugging algorithm on segments.

bool Trace::shrink_segments (Trace::Segments &segments, int expected) {
  size_t n = segments.size ();
  if (!n)
    return false;
  size_t granularity = n;
  bool *removed = new bool[n];
  bool *saved = new bool[n];
  bool *ignore = new bool[size ()];
  for (size_t i = 0; i < n; i++)
    removed[i] = false;
  bool res = false;
  Trace tmp2;
  tmp2.clear ();
  Trace *tmp_notify = this;
  for (;;) {
    for (size_t l = 0, r; l < n; l = r) {
      r = l + granularity;
      if (r > n)
        r = n;
      size_t flipped = 0;
      for (size_t i = 0; i < n; i++)
        saved[i] = false;
      for (size_t i = l; i < r; i++)
        if (!(saved[i] = removed[i]))
          removed[i] = true, flipped++;
      if (!flipped)
        continue;
      for (size_t i = 0; i < size (); i++)
        ignore[i] = false;
      for (size_t i = 0; i < n; i++) {
        if (!removed[i])
          continue;
        Segment &s = segments[i];
        for (size_t j = s.lo; j < s.hi; j++)
          if (!calls[j]->matching_type ())
            ignore[j] = true;
      }
      Trace tmp;
      tmp.clear ();
      for (size_t i = 0; i < size (); i++)
        if (!ignore[i])
          tmp.push_back (calls[i]->copy ());
      progress (*tmp_notify);
      if (tmp.fork_and_execute () != expected) { // failed
        for (size_t i = l; i < r; i++)
          removed[i] = saved[i];
      } else {
        res = true; // succeeded to shrink
        mobical.notify (tmp);
        tmp2.clear ();
        for (size_t i = 0; i < tmp.size (); i++) {
          tmp2.push_back (tmp.calls[i]->copy ());
          tmp_notify = &tmp2;
        }
      }
    }
    if (granularity == 1)
      break;
    granularity = (granularity + 1) / 2;
  }
  if (res) {
    for (size_t i = 0; i < size (); i++)
      ignore[i] = false;
    for (size_t i = 0; i < n; i++) {
      if (!removed[i])
        continue;
      Segment &s = segments[i];
      for (size_t j = s.lo; j < s.hi; j++)
        if (!calls[j]->matching_type ())
          ignore[j] = true;
    }
    size_t j = 0;
    for (size_t i = 0; i < size (); i++) {
      Call *c = calls[i];
      if (ignore[i])
        delete c;
      else
        calls[j++] = c;
    }
    calls.resize (j);
    notify ();
  }
  delete[] ignore;
  delete[] removed;
  delete[] saved;
  return res;
}

/*------------------------------------------------------------------------*/

void Mobical::summarize (Trace &trace, bool bright) {
  if (bright)
    terminal.cyan (bright);
  else
    terminal.blue ();
  cerr << right << setw (5) << trace.size ();
  terminal.normal ();
  cerr << ' ';
  terminal.magenta (bright);
  cerr << ' ' << right << setw (3) << trace.vars ();
  terminal.yellow (bright);
  cerr << ' ' << left << setw (4) << trace.clauses ();
  terminal.normal ();
  cerr << ' ';
  if (bright)
    terminal.cyan (bright);
  else
    terminal.blue ();
  cerr << setw (2) << right << trace.phases ();
  terminal.normal ();
}

void Mobical::notify (Trace &trace, signed char ch) {
  if (quiet)
    return;
  bool first = notified.empty ();
#ifdef QUIET
  if (ch < 0)
    return;
  if (ch > 0)
    notified.push_back (ch);
#else
  if (ch < 0 && (!terminal || verbose))
    return;
  double t = absolute_real_time ();
  if (ch > 0)
    notified.push_back (ch), progress_counter = 1;
  else if (ch < 0) {
    if (t < last_progress_time + 0.3)
      return;
    progress_counter++;
  }
#endif
  if (!first || !(mode & OUTPUT))
    terminal.erase_line_if_connected_otherwise_new_line ();
  prefix ();
  if (traces)
    cerr << ' ' << left << setw (12) << traces;
  else
    cerr << left << "red: " << setw (8) << trace.executed;
  terminal.yellow ();

  if (!notified.empty ()) {
    for (size_t i = 0; i + 1 < notified.size (); i++)
      cerr << notified[i];
#ifndef QUIET
    if (progress_counter & 1)
      terminal.inverse ();
#else
    terminal.inverse ();
#endif
    cerr << notified.back ();
    terminal.normal ();
  }

  if (notified.size () < 45)
    cerr << setw (45 - notified.size ()) << " ";
  cerr << flush;
  summarize (trace);
  if (verbose)
    cerr << endl;
  cerr << flush;
#ifndef QUIET
  last_progress_time = t;
#endif
}

/*------------------------------------------------------------------------*/

// Explicit grammar aware three-level hierarchical delta-debugging.
// First level is in term of incremental solving phases where one phase
// consists of maximal prefixes of intervals of calls of type
// '(BEFORE*| PROCESS | DURING* | AFTER*)' or single non-configuration
// calls.
//
bool Trace::shrink_phases (int expected) {
  if (mobical.donot.shrink.phases)
    return false;
  notify ('p');
  size_t l;
  for (l = 1; l < size () && calls[l]->config_type (); l++)
    ;
  Segments segments;
  size_t r;
  for (; l < size (); l = r) {
    for (r = l; r < size () && calls[r]->before_type (); r++)
      ;
    if (r < size () && calls[r]->process_type ())
      r++;
    for (; r < size () && calls[r]->during_type (); r++)
      ;
    for (; r < size () && calls[r]->after_type (); r++)
      ;
    if (l < r)
      segments.push_back (Segment (l, r));
    else {
      assert (l == r);
      if (!calls[r]->config_type () && !calls[r]->matching_type ()) {
        segments.push_back (Segment (r, r + 1));
      }
      ++r;
    }
  }
  return shrink_segments (segments, expected);
}

// The second level tries to remove clauses.
//
bool Trace::shrink_clauses (int expected) {
  if (mobical.donot.shrink.clauses)
    return false;
  notify ('c');
  Segments segments;
  for (size_t r = size (), l; r > 1; r = l) {
    Call *c = calls[l = r - 1];
    while (l > 0 && (!c->is_clause_type () || c->arg))
      c = calls[--l];
    if (!l)
      break;
    r = l + 1;
    const uint64_t same = c->type;
    while ((c = calls[--l])->type == same && c->arg)
      ;
    segments.push_back (Segment (++l, r));
  }
  return shrink_segments (segments, expected);
}

// The third level tries to remove individual literals.
//
bool Trace::shrink_literals (int expected) {
  if (mobical.donot.shrink.literals)
    return false;
  notify ('l');
  Segments segments;
  for (size_t l = size () - 1; l > 0; l--) {
    Call *c = calls[l];
    if (c->is_clause_type () && c->arg)
      segments.push_back (Segment (l, l + 1));
  }
  return shrink_segments (segments, expected);
}

// first remove all propagator_type calls.
// if unsuccessful, remove all possible pairs of
// subsequent (disconnect, connect)
// lastly, remove possible pairs of
// (connect, disconnect) with propagator calls in between
bool Trace::shrink_propagator (int expected) {
  if (mobical.donot.shrink.propagator)
    return false;
  notify ('e');
  Trace simplified;
  size_t connected = 0;
  size_t disconnected = 0;
  for (auto c : calls) {
    if (c->type == Call::CONNECT) {
      connected++;
      continue;
    }
    if (c->type == Call::DISCONNECT) {
      disconnected++;
      continue;
    }
    if (c->propagator_type ())
      continue;
    simplified.push_back (c->copy ());
  }
  progress ();
  if (!connected) {
    assert (simplified.calls.size () == calls.size ());
    notify ();
    return false;
  }
  assert (simplified.calls.size () < calls.size ());
  if (simplified.fork_and_execute () == expected) {
    clear ();
    for (auto c : simplified.calls)
      push_back (c->copy ());
    notify ();
    return true;
  }
  simplified.clear ();
  bool reduced = false;
  while (disconnected--) {
    bool remove_next_connect = false;
    size_t num_disconnect = 0;
    bool removed_connected = false;
    for (auto c : calls) {
      if (c->type == Call::DISCONNECT && disconnected == num_disconnect++) {
        remove_next_connect = true;
        continue;
      }
      if (c->type == Call::CONNECT && remove_next_connect) {
        remove_next_connect = false;
        removed_connected = true;
        continue;
      }
      simplified.push_back (c->copy ());
    }
    assert (simplified.calls.size () < calls.size ());
    if (simplified.fork_and_execute () == expected) {
      if (removed_connected)
        connected--;
      clear ();
      for (auto c : simplified.calls)
        push_back (c->copy ());
      simplified.clear ();
      reduced = true;
      progress ();
    }
  }
  while (connected--) {
    bool remove_next_disconnect = false;
    size_t num_connect = 0;
    for (auto c : calls) {
      if (c->type == Call::CONNECT && connected == num_connect++) {
        remove_next_disconnect = true;
        continue;
      }
      if (c->type == Call::DISCONNECT && remove_next_disconnect) {
        remove_next_disconnect = false;
        continue;
      }
      if (c->propagator_type () && remove_next_disconnect) {
        continue;
      }
      simplified.push_back (c->copy ());
    }
    assert (simplified.calls.size () < calls.size ());
    if (simplified.fork_and_execute () == expected) {
      clear ();
      for (auto c : simplified.calls)
        push_back (c->copy ());
      reduced = true;
      simplified.clear ();
      progress ();
    }
  }
  notify ();
  return reduced;
}

bool Trace::shrink_basic (int expected) {
  if (mobical.donot.shrink.basic)
    return false;
  notify ('b');
  Segments segments;
  for (size_t l = size () - 1; l > 0; l--) {
    Call *c = calls[l];
    if (!c->is_basic ())
      continue;
    segments.push_back (Segment (l, l + 1));
  }
  return shrink_segments (segments, expected);
}

// We first add all non present possible options with their default value.

void Trace::add_options (int expected) {
  if (mobical.donot.add)
    return;
  const int max_var = vars ();
  notify ('a');
  assert (size ());
  Trace extended;
  size_t i = 0;
  Call *c;
  for (; i < size (); i++) {
    c = calls[i];
#ifdef MOBICAL_MEMORY
    if (!(c->type == Call::INIT || c->type == Call::MAXALLOC))
#else
    if (!(c->type == Call::INIT))
#endif
    {
      continue;
    }
    extended.push_back (c->copy ());
  }
  while (i < size () && (c = calls[i])->type == Call::SET)
    extended.push_back (c->copy ()), i++;
  for (Options::const_iterator it = Options::begin ();
       it != Options::end (); it++) {
    const Option &o = *it;
    if (find_option_by_name (o.name))
      continue;
    if (ignore_option (o.name, max_var))
      continue;
    if (extended.ignore_option (o.name, max_var))
      continue;
    extended.push_back (new SetCall (o.name, o.def));
  }
  while (i < size ())
    extended.push_back (calls[i++]->copy ());
  progress ();
  if (extended.fork_and_execute () != expected)
    return;
  clear ();
  for (i = 0; i < extended.size (); i++)
    push_back (extended[i]->copy ());
  notify ();
}

// Try to set as many options to their lower limit, which also tries to
// disable as many boolean options.

bool Trace::shrink_disable (int expected) {
  if (mobical.donot.disable)
    return false;
  const int max_var = vars ();

  notify ('d');
  size_t last = last_option ();
  vector<size_t> candidates;
  vector<int> lower, saved;
  for (size_t i = first_option (); i < last; i++) {
    Call *c = calls[i];
    if (c->type != Call::SET)
      continue;
    if (ignore_option (c->name, max_var))
      continue;
    Option *o = Options::has (c->name);
    if (!o)
      continue;
    if (c->val == o->lo)
      continue;
    candidates.push_back (i);
    lower.push_back (o->lo);
    saved.push_back (c->val);
  }
  if (candidates.empty ())
    return false;
  size_t granularity = candidates.size ();
  bool res = false;
  for (;;) {
    size_t n = candidates.size ();
    for (size_t i = 0; i < n; i += granularity) {
      bool reduce = false;
      for (size_t j = i; j < n && j < i + granularity; j++) {
        size_t k = candidates[j];
        Call *c = calls[k];
        assert (c->type == Call::SET);
        saved[j] = c->val;
        int new_val = lower[j];
        if (c->val == new_val)
          continue;
        c->val = new_val;
        reduce = true;
      }
      if (!reduce)
        continue;
      progress ();
      if (fork_and_execute () == expected)
        res = true;
      else {
        for (size_t j = i; j < n && j < i + granularity; j++) {
          size_t k = candidates[j];
          Call *c = calls[k];
          assert (c->type == Call::SET);
          c->val = saved[j];
        }
      }
    }
    if (granularity == 1)
      break;
    granularity = (granularity + 1) / 2;
  }
  notify ();
  return res;
}

// Try to shrink the option values.

bool Trace::reduce_values (int expected) {
  if (mobical.donot.reduce)
    return false;

  notify ('r');

  assert (size ());

  bool changed = false, res = false;
  do {
    if (changed)
      res = true;
    changed = false;
    for (size_t i = 0; i < size (); i++) {
      Call *c = calls[i];

      int lo, hi;

      if (c->type == Call::SET) {
        Option *o = Options::has (c->name);
        if (!o)
          continue;
        lo = o->lo, hi = o->hi;
      } else if (c->type == Call::LIMIT) {
        if (!strcmp (c->name, "conflicts") ||
            !strcmp (c->name, "decisions"))
          lo = -1, hi = INT_MAX;
        else if (!strcmp (c->name, "terminate") ||
                 !strcmp (c->name, "preprocessing"))
          lo = 0, hi = INT_MAX;
        else if (!strcmp (c->name, "localsearch"))
          lo = 0, hi = c->val; // too costly otherwise
        else
          continue;
      } else if (c->type == Call::OPTIMIZE) {
        lo = 0, hi = 9;
#ifdef MOBICAL_TERMINATE
      } else if (c->type == Call::TERMINATE) {
        lo = 0, hi = c->val;
#endif
#ifdef MOBICAL_MEMORY
      } else if (c->type == Call::MAXALLOC) {
        lo = 0, hi = c->val;
#endif
      } else if (c->type == Call::DECIDE) {
        lo = 0, hi = c->val;
      } else if (c->type == Call::LEMMA) {
        lo = 0, hi = c->val;
      } else if (c->type == Call::FORCE) {
        lo = 0, hi = c->val;
      } else
        continue;

      assert (lo <= hi);
      if (c->val == lo)
        continue;

      // First try to reach eagerly the low value
      // (includes the case that current value is too low).
      //
      int old_val = c->val;
      c->val = lo;
      progress ();
      if (fork_and_execute () == expected) {
        assert (c->val != old_val);
        changed = true;
        continue;
      }
      c->val = old_val;

      // Then try to limit to the high value if current value too large.
      //
      if (c->val > hi) {
        int old_val = c->val;
        c->val = hi;
        progress ();
        if (fork_and_execute () == expected) {
          assert (c->val != old_val);
          changed = true;
        } else {
          c->val = old_val;
          continue;
        }
      }

      // Now we do a delta-debugging inspired binary search for the
      // smallest value for which the execution produces a non-zero exit
      // code.  It kind of assumes monotonicity and if this is not the
      // case might not yield the smallest value, but remains logarithmic.
      //
      int64_t granularity = ((old_val - (int64_t) lo) + 1l) / 2;
      assert (granularity > 0);
      for (int64_t new_val = c->val - granularity; new_val > lo;
           new_val -= granularity) {
        old_val = c->val;
        assert (new_val != old_val);
        assert (lo < new_val);
        assert (new_val <= hi);
        c->val = new_val;
        progress ();
        if (fork_and_execute () == expected) {
          assert (c->val != old_val);
          changed = true;
        } else
          c->val = old_val;
      }
    }
  } while (changed);

  notify ();

  return res;
}

// Try to map variables to a contiguous initial range.

void Trace::map_variables (int expected) {
  if (mobical.donot.map)
    return;
  for (int with_gaps = 0; with_gaps <= 1; with_gaps++) {
    notify ('m');
    vector<int> variables;
    for (size_t i = 0; i < size (); i++) {
      Call *c = calls[i];
      if (!c->lit_type ())
        continue;
      if (!c->arg)
        continue;
      if (c->arg == INT_MIN)
        continue;
      int idx = abs (c->arg);
      if (variables.size () <= (size_t) idx)
        variables.resize (1 + (size_t) idx, 0);
      variables[idx]++;
    }
    int gaps = 0, max_idx = 0;
    bool skipped = false;
    for (int i = 1; (size_t) i < variables.size (); i++) {
      if (!variables[i]) {
        if (with_gaps && !skipped)
          max_idx++, skipped = true;
        gaps++;
      } else {
        variables[i] = ++max_idx;
        skipped = false;
      }
    }
    if (!gaps) {
      notify ();
      return;
    }
    Trace mapped;
    for (size_t i = 0; i < size (); i++) {
      Call *c = calls[i];
      if (!c->lit_type ())
        mapped.push_back (c->copy ());
      else if (!c->arg || c->arg == INT_MIN)
        mapped.push_back (c->copy ());
      else {
        int new_lit = variables[abs (c->arg)];
        assert (0 < new_lit), assert (new_lit <= max_idx);
        if (c->arg < 0)
          new_lit = -new_lit;
        Call *d = c->copy ();
        d->arg = new_lit;
        mapped.push_back (d);
      }
    }
    progress ();
    if (mapped.fork_and_execute () == expected) {
      clear ();
      for (size_t i = 0; i < mapped.size (); i++)
        push_back (mapped[i]->copy ());
      notify ();
      with_gaps = 2;
    }
    notify ();
  }
}

// Finally remove option calls.

void Trace::shrink_options (int expected) {
  if (mobical.donot.shrink.options)
    return;

  notify ('o');
  Segments segments;
  for (size_t i = 0; i < size (); i++) {
    Call *c = calls[i];
    if (c->type != Call::SET)
      continue;
    segments.push_back (Segment (i, i + 1));
  }

  (void) shrink_segments (segments, expected);
}

void Trace::shrink (int expected) {
  enum Shrinking {
    NONE = 0,
    PHASES,
    CLAUSES,
    LITERALS,
    PROPAGATOR,
    BASIC,
    DISABLE,
    VALUES
  };

  mobical.shrinking = true;
  mobical.notified.clear ();
  assert (!mobical.donot.shrink.atall);
  if (!size ())
    return;
  add_options (expected);
  Shrinking l = NONE;
  bool s;
  do {
    s = false;
    if (l != PHASES && shrink_phases (expected))
      s = true, l = PHASES;
    if (l != PROPAGATOR && shrink_propagator (expected))
      s = true, l = PROPAGATOR;
    if (l != CLAUSES && shrink_clauses (expected))
      s = true, l = CLAUSES;
    if (l != LITERALS && shrink_literals (expected))
      s = true, l = LITERALS;
    if (l != BASIC && shrink_basic (expected))
      s = true, l = BASIC;
    if (l != DISABLE && shrink_disable (expected))
      s = true, l = DISABLE;
    if (l != VALUES && reduce_values (expected))
      s = true, l = VALUES;
  } while (s);
  map_variables (expected);
  shrink_options (expected);
  // Execute one last time to get accurate results when memory fuzzing
  // is enabled.
  fork_and_execute ();
  cerr << flush;
  mobical.shrinking = false;
}

void Trace::write_path (const char *path, int code) {
  if (!strcmp (path, "-"))
    print (cout, code);
  else {
    ofstream os (path);
    if (!os.is_open ())
      mobical.die ("can not write '%s'", path);
    print (os, code);
  }
}

void Trace::write_prefixed_seed (const char *prefix, int code) {
  ostringstream ss;
  ss << prefix << '-' << setfill ('0') << right << setw (20) << seed
     << ".trace" << flush;
  ofstream os (ss.str ().c_str ());
  if (!os.is_open ())
    mobical.die ("can not write '%s'", ss.str ().c_str ());
  print (os, code);
  cerr << ss.str ();
}

/*------------------------------------------------------------------------*/

void Reader::error (const char *fmt, ...) {
  mobical.error_prefix ();
  mobical.terminal.red (true);
  fputs ("parse error:", stderr);
  mobical.terminal.normal ();
  fprintf (stderr, " %s:%d: ", path, lineno);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  mobical.terminal.reset ();
  exit (1);
}

static bool is_valid_char (int ch) {
  if (ch == ' ')
    return true;
  if (ch == '-')
    return true;
  if ('a' <= ch && ch <= 'z')
    return true;
  if ('0' <= ch && ch <= '9')
    return true;

  // For now proof file paths can only have these additional characters.
  // We should probably have an escape mechamism (quotes) for paths.

  if (ch == '_' || ch == '/' || ch == '.' || ('A' <= ch && ch <= 'Z'))
    return true;

  return false;
}

void Reader::parse () {
  int ch, lit = 0, val = 0, solved = 0;
  uint64_t state = 0, adding = 0;
  Call *prev = 0;
  const bool enforce = !mobical.donot.enforce;
  Call *before_trigger = 0;
  bool connected = 0;
  char line[80];
  while ((ch = next ()) != EOF) {
    // Ignore comments (used for additional human readable information).
    if (ch == '#') {
      while (ch != '\n') {
        if ((ch = next ()) == EOF)
          error ("unexpected end-of-file");
      }
      continue;
    }
    size_t n = 0;
    while (ch != '\n') {
      if (n + 2 >= sizeof line)
        error ("line too large");
      if (!is_valid_char (ch)) {
        if (isprint (ch))
          error ("invalid character '%c'", ch);
        else
          error ("invalid character code 0x%02x", ch);
      }
      line[n++] = ch;
      if ((ch = next ()) == EOF)
        error ("unexpected end-of-file");
      // Comments at the end of the line
      if (ch == ' ' && peek () == '#') {
        while (ch != '\n') {
          if ((ch = next ()) == EOF)
            error ("unexpected end-of-file");
        }
      }
    }
    assert (n < sizeof line);
    line[n] = 0;
    char *p = line;
    if (isdigit (*p)) {
      while (isdigit (ch = *++p))
        ;
      if (!ch)
        error ("incomplete line with only line number");
      if (ch != ' ')
        error ("expected space after line number");
      p++;
    }
    const char *keyword = p;
    if ((ch = *p) < 'a' || 'z' < ch)
      error ("expected keyword to start with lower case letter");
    while (p < line + n && (ch = *++p) &&
           (('a' <= ch && ch <= 'z') || ch == '_'))
      ;
    const char *first = 0, *second = 0, *third = 0;
    bool third_argument = 0;
    if ((ch = *p) == ' ') {
      *p++ = 0;
      first = p;
      ch = *p;
      if (!ch)
        error ("first argument missing after trailing space");
      if (ch == ' ')
        error ("space in place of first argument");
      while ((ch = *++p) && ch != ' ')
        ;
      if (ch == ' ') {
        *p++ = 0;
        second = p;
        ch = *p;
        if (!ch)
          error ("second argument missing after trailing space");
        if (ch == ' ')
          error ("space in place of second argument");
        while ((ch = *++p) && ch != ' ')
          ;
        if (ch == ' ') {
          *p++ = 0;
          third = p;
          third_argument = 0;
          ch = *p;
          if (!ch)
            error ("third argument missing after trailing space");
          if (ch == ' ')
            error ("space in place of third argument");
          while ((ch = *++p) && ch != ' ')
            ;
          if (ch == ' ') {
            *p = 0;
            error ("unexpected space after third argument '%s'", third);
          }
        }
      }
    } else if (ch)
      error ("unexpected character '%c' in keyword", ch);
    assert (!ch);
    Call *c = 0;
    if (!strcmp (keyword, "init")) {
      if (first)
        error ("unexpected argument '%s' after 'init'", first);
      c = new InitCall ();
    } else if (!strcmp (keyword, "set")) {
      if (!first)
        error ("first argument to 'set' missing");
      if (enforce && !Solver::is_valid_option ((first))) {
#ifndef LOGGING
        if (!strcmp (first, "log"))
          mobical.warning ("ignoring non-existing option name 'log' "
                           "(compiled without '-DLOGGING')");
        else
#endif
          error ("non-existing option name '%s'", first);
      }
      if (!second)
        error ("second argument to 'set' missing");
      if (!parse_int_str (second, val))
        error ("invalid second argument '%s' to 'set'", second);
      c = new SetCall (first, val);
    } else if (!strcmp (keyword, "configure")) {
      if (!first)
        error ("first argument to 'configure' missing");
      if (enforce && !Solver::is_valid_configuration (first))
        error ("non-existing configuration '%s'", first);
      if (second)
        error ("additional argument '%s' to 'configure'", second);
      c = new ConfigureCall (first);
    } else if (!strcmp (keyword, "limit")) {
      if (!first)
        error ("first argument to 'limit' missing");
      if (!second)
        error ("second argument to 'limit' missing");
      if (!parse_int_str (second, val))
        error ("invalid second argument '%s' to 'limit'", second);
      c = new LimitCall (first, val);
    } else if (!strcmp (keyword, "optimize")) {
      if (!first)
        error ("argument to 'optimize' missing");
      if (!parse_int_str (first, val) || val < 0 || val > 31)
        error ("invalid argument '%s' to 'optimize'", first);
      c = new OptimizeCall (val);
    } else if (!strcmp (keyword, "vars")) {
      if (first)
        error ("unexpected argument '%s' after 'vars'", first);
      c = new VarsCall ();
    } else if (!strcmp (keyword, "active")) {
      if (first)
        error ("unexpected argument '%s' after 'active'", first);
      c = new ActiveCall ();
    } else if (!strcmp (keyword, "redundant")) {
      if (first)
        error ("unexpected argument '%s' after 'redundant'", first);
      c = new RedundantCall ();
    } else if (!strcmp (keyword, "irredundant")) {
      if (first)
        error ("unexpected argument '%s' after 'irredundant'", first);
      c = new IrredundantCall ();
    } else if (!strcmp (keyword, "resize")) {
      if (!first)
        error ("argument to 'resize' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'resize'", first);
      if (second)
        error ("additional argument '%s' to 'resize'", second);
      c = new ResizeCall (lit);
    } else if (!strcmp (keyword, "declare_vars")) {
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'declare_vars'", first);
      c = new DeclareMoreVariablesCall (lit);
    } else if (!strcmp (keyword, "phase")) {
      if (!first)
        error ("argument to 'phase' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'phase'", first);
      if (second)
        error ("additional argument '%s' to 'phase'", second);
      c = new PhaseCall (lit);
    } else if (!strcmp (keyword, "unphase")) {
      if (!first)
        error ("argument to 'unphase' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'unphase'", first);
      if (second)
        error ("additional argument '%s' to 'unphase'", second);
      c = new UnPhaseCall (lit);
    } else if (!strcmp (keyword, "add")) {
      if (!first)
        error ("argument to 'add' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'add'", first);
      if (second)
        error ("additional argument '%s' to 'add'", second);
      if (enforce && lit == INT_MIN)
        error ("invalid literal '%d' as argument to 'add'", lit);
      adding = lit ? (uint64_t) Call::ADD : 0;
      c = new AddCall (lit);
    } else if (!strcmp (keyword, "constrain")) {
      if (!first)
        error ("argument to 'constrain' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'constrain'", first);
      if (second)
        error ("additional argument '%s' to 'constrain'", second);
      if (enforce && lit == INT_MIN)
        error ("invalid literal '%d' as argument to 'constrain'", lit);
      adding = lit ? (uint64_t) Call::CONSTRAIN : 0;
      c = new ConstrainCall (lit);
    } else if (!strcmp (keyword, "connect")) {
      c = new ConnectCall ();
    } else if (!strcmp (keyword, "disconnect")) {
      c = new DisconnectCall ();
    } else if (!strcmp (keyword, "declare_var")) {
      c = new DeclareOneMoreVariableCall ();
    } else if (!strcmp (keyword, "observe")) {
      if (!first)
        error ("argument to 'observe' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'observe'", first);
      if (enforce && (!lit || lit == INT_MIN))
        error ("invalid argument '%s' to 'observe'", first);
      if (second)
        error ("additional argument '%s' to 'observe'", second);
      c = new ObserveCall (lit);
    } else if (!strcmp (keyword, "unobserve")) {
      if (!first)
        error ("argument to 'unobserve' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'unobserve'", first);
      if (enforce && (!lit || lit == INT_MIN))
        error ("invalid argument '%s' to 'unobserve'", first);
      if (second)
        error ("additional argument '%s' to 'unobserve'", second);
      c = new UnObserveCall (lit);
    } else if (!strcmp (keyword, "lemma")) {
      if (!first)
        error ("argument to 'lemma' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'lemma'", first);
      if (lit && second)
        error ("additional argument '%s' to 'lemma'", second);
      if (enforce && lit == INT_MIN)
        error ("invalid literal '%d' as argument to 'lemma'", lit);
      adding = lit ? (uint64_t) Call::LEMMA : 0;
      LemmaType tmpt = LAZY;
      int tmp = 0;
      if (second) {
        if (!parse_int_str (second, tmp))
          error ("invalid argument '%s' to 'lemma %d'", lit, second);
        tmpt = static_cast<LemmaType> (tmp);
        if (enforce && static_cast<int> (tmpt) != tmp)
          error ("invalid argument '%s' to 'lemma %d'", second, lit);
        if (enforce && tmp == LAST_LEMMA_TYPE)
          error ("invalid argument '%s' to 'lemma %d'", second, lit);
      }
      val = 0;
      if (third) {
        if (!parse_int_str (third, val))
          error ("invalid argument '%s' to 'lemma'", third);
      }
      if (mobical.donot.mock_propagator)
        error ("cannot execute 'lemma' (try without '--no-mock')");
      c = new LemmaCall (lit, tmpt, val);
      third_argument = true;
    } else if (!strcmp (keyword, "force")) {
      if (!first)
        error ("argument to 'force' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'force'", first);
      if (enforce && lit == INT_MIN)
        error ("invalid literal '%d' as argument to 'force'", lit);
      MockForceType tmpt;
      int tmp = 0;
      if (!second)
        error ("second argument to 'force %d' missing", lit);
      if (!parse_int_str (second, tmp))
        error ("invalid second argument '%s' to 'force %d'", lit, second);
      tmpt = static_cast<MockForceType> (tmp);
      if (enforce && static_cast<int> (tmpt) != tmp)
        error ("invalid argument '%s' to 'force %d'", second, lit);
      if (enforce && tmp == LAST_MOCK_FORCE_TYPE)
        error ("invalid argument '%s' to 'force %d'", second, lit);
      if (!third)
        error ("third argument to 'force %d %s' missing", lit, second);
      if (!parse_int_str (third, val))
        error ("invalid argument '%s' to 'force %d %d'", third, lit, tmp);
      if (mobical.donot.mock_propagator)
        error ("cannot execute 'force' (try without '--no-mock')");
      c = new MockForceCall (lit, tmpt, val);
      third_argument = true;
    } else if (!strcmp (keyword, "decide")) {
      if (!first)
        error ("argument to 'decide' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'decide'", first);
      if (enforce && lit == INT_MIN)
        error ("invalid literal '%d' as argument to 'decide'", lit);
      if (!second)
        error ("second argument to 'decide %d' missing", lit);
      if (!parse_int_str (second, val))
        error ("invalid second argument '%s' to 'decide'", second);
      if (mobical.donot.mock_propagator)
        error ("cannot execute 'decide' (try without '--no-mock')");
      c = new DecideCall (lit, val);
    } else if (!strcmp (keyword, "notify_assignment")) {
      if (!first)
        error ("argument to 'notify_assignment' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'notify_assignment'", first);
      if (enforce && lit == INT_MIN)
        error ("invalid literal '%d' as argument to 'notify_assignment'",
               lit);
      if (second)
        error ("additional argument '%s' to 'notify_assignment %d'", second,
               lit);
      if (!mobical.donot.mock_propagator)
        error ("cannot execute 'notify_assignment' (try with '--no-mock')");
      c = new NotifyAssignmentCall (lit);
    } else if (!strcmp (keyword, "notify_assignment_batch")) {
      if (!first)
        error ("argument to 'notify_assignment_batch' missing");
      if (!parse_int_str (first, val))
        error ("invalid argument '%s' to 'notify_assignment_batch'", first);
      if (enforce && val <= 0)
        error (
            "invalid value '%d' as argument to 'notify_assignment_batch'",
            val);
      if (second)
        error ("additional argument '%s' to 'notify_assignment_batch %d'",
               second, val);
      if (!mobical.donot.mock_propagator)
        error ("cannot execute 'notify_assignment_batch' (try with "
               "'--no-mock')");
      c = new NotifyBatchAssignmentCall (val);
    } else if (!strcmp (keyword, "notify_backtrack")) {
      if (!first)
        error ("argument to 'notify_backtrack' missing");
      if (!parse_int_str (first, val))
        error ("invalid argument '%s' to 'notify_backtrack'", first);
      if (enforce && val < 0)
        error ("invalid level '%d' as argument to 'notify_backtrack'", val);
      if (second)
        error ("additional argument '%s' to 'notify_backtrack %d'", second,
               val);
      if (!mobical.donot.mock_propagator)
        error ("cannot execute 'notify_backtrack' (try with '--no-mock')");
      c = new NotifyBacktrackCall (val);
    } else if (!strcmp (keyword, "notify_new_decision_level")) {
      if (first)
        error ("additional argument '%s' to 'notify_new_decision_level'",
               first);
      if (!mobical.donot.mock_propagator)
        error ("cannot execute 'notify_new_decision_level' (try with "
               "'--no-mock')");
      c = new NotifyLevelCall ();
    } else if (!strcmp (keyword, "cb_decide")) {
      if (!first)
        error ("argument to 'cb_decide' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'cb_decide'", first);
      if (enforce && lit == INT_MIN)
        error ("invalid literal '%d' as argument to 'cb_decide'", lit);
      if (second)
        error ("additional argument '%s' to 'cb_decide %d'", second, lit);
      if (!mobical.donot.mock_propagator)
        error ("cannot execute 'cb_decide' (try with '--no-mock')");
      c = new CBDecideCall (lit);
    } else if (!strcmp (keyword, "is_decision")) {
      if (!first)
        error ("argument to 'is_decision' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'is_decision'", first);
      if (enforce && lit == INT_MIN)
        error ("invalid literal '%d' as argument to 'is_decision'", lit);
      if (!second)
        error ("second argument to 'is_decision' missing");
      if (!parse_int_str (second, val))
        error ("invalid second argument '%s' to 'is_decision %d'", second,
               lit);
      c = new IsDecisionCall (lit, val);
    } else if (!strcmp (keyword, "current_value")) {
      if (!first)
        error ("argument to 'current_value' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'current_value'", first);
      if (enforce && lit == INT_MIN)
        error ("invalid literal '%d' as argument to 'current_value'", lit);
      if (!second)
        error ("second argument to 'current_value' missing");
      if (!parse_int_str (second, val))
        error ("invalid second argument '%s' to 'current_value %d'", second,
               lit);
      c = new CurrentValueCall (lit, val);
    } else if (!strcmp (keyword, "cb_add_reason_clause_lit")) {
      if (!first)
        error ("argument to 'cb_add_reason_clause_lit' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'cb_add_reason_clause_lit'",
               first);
      if (enforce && lit == INT_MIN)
        error ("invalid literal '%d' as argument to "
               "'cb_add_reason_clause_lit'",
               lit);
      if (second)
        error ("additional argument '%s' to 'cb_add_reason_clause_lit %d'",
               second, lit);
      if (!mobical.donot.mock_propagator)
        error ("cannot execute 'cb_add_reason_clause_lit' (try with "
               "'--no-mock')");
      c = new CBAddReasonCall (lit);
    } else if (!strcmp (keyword, "cb_add_external_clause_lit")) {
      if (!first)
        error ("argument to 'cb_add_external_clause_lit' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'cb_add_external_clause_lit'",
               first);
      if (enforce && lit == INT_MIN)
        error ("invalid literal '%d' as argument to "
               "'cb_add_external_clause_lit'",
               lit);
      if (second)
        error (
            "additional argument '%s' to 'cb_add_external_clause_lit %d'",
            second, lit);
      if (!mobical.donot.mock_propagator)
        error ("cannot execute 'cb_add_external_clause_lit' (try with "
               "'--no-mock')");
      c = new CBAddClauseCall (lit);
    } else if (!strcmp (keyword, "cb_has_external_clause_lit")) {
      if (!first)
        error ("argument to 'cb_has_external_clause_lit' missing");
      if (!parse_int_str (first, val))
        error ("invalid argument '%s' to 'cb_has_external_clause_lit'",
               first);
      if (enforce && val != 0 && val != 1)
        error ("invalid literal '%d' as argument to "
               "'cb_has_external_clause_lit'",
               val);
      if (second)
        error (
            "additional argument '%s' to 'cb_has_external_clause_lit %d'",
            second, val);
      if (!mobical.donot.mock_propagator)
        error ("cannot execute 'cb_has_external_clause_lit' (try with "
               "'--no-mock')");
      c = new CBHasClauseCall (val);
    } else if (!strcmp (keyword, "cb_check_found_model")) {
      if (!first)
        error ("argument to 'cb_check_found_model' missing");
      if (!parse_int_str (first, val))
        error ("invalid argument '%s' to 'cb_check_found_model'", first);
      if (enforce && val != 0 && val != 1)
        error ("invalid literal '%d' as argument to "
               "'cb_check_found_model'",
               val);
      if (second)
        error ("additional argument '%s' to 'cb_check_found_model %d'",
               second, val);
      if (!mobical.donot.mock_propagator)
        error (
            "cannot execute 'cb_check_found_model' (try with '--no-mock')");
      c = new CBCheckModelCall (val);
    } else if (!strcmp (keyword, "assume")) {
      if (!first)
        error ("argument to 'assume' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'assume'", first);
      if (second)
        error ("additional argument '%s' to 'assume'", second);
      if (enforce && (!lit || lit == INT_MIN))
        error ("invalid literal '%d' as argument to 'assume'", lit);
      c = new AssumeCall (lit);
    } else if (!strcmp (keyword, "solve")) {
      if (first && !parse_int_str (first, lit))
        error ("invalid argument '%s' to 'solve'", first);
      if (first && lit != 0 && lit != 10 && lit != 20)
        error ("invalid result argument '%d' to 'solve'", lit);
      assert (!second);
      if (first)
        c = new SolveCall (lit);
      else
        c = new SolveCall ();
      solved++;
    } else if (!strcmp (keyword, "simplify")) {
      if (!first)
        error ("argument to 'simplify' missing");
      int rounds;
      if (!parse_int_str (first, rounds) || rounds < 0)
        error ("invalid argument '%s' to 'simplify'", first);
      int tmp;
      if (second && !parse_int_str (second, tmp))
        error ("invalid second argument '%s' to 'simplify'", second);
      if (second && tmp != 0 && tmp != 10 && tmp != 20)
        error ("invalid second argument '%d' to 'solve'", tmp);
      if (second)
        c = new SimplifyCall (rounds, tmp);
      else
        c = new SimplifyCall (rounds);
      solved++;
    } else if (!strcmp (keyword, "lookahead")) {
      if (first && !parse_int_str (first, lit))
        error ("invalid argument '%s' to 'lookahead'", first);
      assert (!second);
      if (first)
        c = new LookaheadCall (lit);
      else
        c = new LookaheadCall ();
      solved++;
    } else if (!strcmp (keyword, "cubing")) {
      if (first && !parse_int_str (first, lit))
        error ("invalid argument '%s' to 'cubing'", first);
      assert (!second);
      c = new CubingCall (lit);
      solved++;
    } else if (!strcmp (keyword, "propagate")) {
      if (first && !parse_int_str (first, lit))
        error ("invalid argument '%s' to 'solve'", first);
      if (first && lit != 0 && lit != 10 && lit != 20)
        error ("invalid result argument '%d' to 'solve'", lit);
      assert (!second);
      if (first)
        c = new PropagateImplyCall (lit);
      else
        c = new PropagateImplyCall ();
    } else if (!strcmp (keyword, "val")) {
      if (!first)
        error ("first argument to 'val' missing");
      if (!parse_int_str (first, lit))
        error ("invalid first argument '%s' to 'val'", first);
      if (enforce && (!lit || lit == INT_MIN))
        error ("invalid literal '%d' as argument to 'val'", lit);
      if (second && !parse_int_str (second, val))
        error ("invalid second argument '%s' to 'val'", second);
      if (second && val != -1 && val != 0 && val != 1)
        error ("invalid result argument '%d' to 'val", val);
      if (second)
        c = new ValCall (lit, val);
      else
        c = new ValCall (lit);
    } else if (!strcmp (keyword, "flip")) {
      if (!first)
        error ("first argument to 'flip' missing");
      if (!parse_int_str (first, lit))
        error ("invalid first argument '%s' to 'flip'", first);
      if (enforce && (!lit || lit == INT_MIN))
        error ("invalid literal '%d' as argument to 'flip'", lit);
      if (second && !parse_int_str (second, val))
        error ("invalid second argument '%s' to 'flip'", second);
      if (second && val != 0 && val != 1)
        error ("invalid result argument '%d' to 'flip", val);
      if (second)
        c = new FlipCall (lit, val);
      else
        c = new FlipCall (lit);
    } else if (!strcmp (keyword, "flippable")) {
      if (!first)
        error ("first argument to 'flippable' missing");
      if (!parse_int_str (first, lit))
        error ("invalid first argument '%s' to 'flippable'", first);
      if (enforce && (!lit || lit == INT_MIN))
        error ("invalid literal '%d' as argument to 'flippable'", lit);
      if (second && !parse_int_str (second, val))
        error ("invalid second argument '%s' to 'flippable'", second);
      if (second && val != 0 && val != 1)
        error ("invalid result argument '%d' to 'flippable", val);
      if (second)
        c = new FlippableCall (lit, val);
      else
        c = new FlippableCall (lit);
    } else if (!strcmp (keyword, "fixed")) {
      if (!first)
        error ("first argument to 'fixed' missing");
      if (!parse_int_str (first, lit))
        error ("invalid first argument '%s' to 'fixed'", first);
      if (enforce && (!lit || lit == INT_MIN))
        error ("invalid literal '%d' as argument to 'fixed'", lit);
      if (second && !parse_int_str (second, val))
        error ("invalid second argument '%s' to 'fixed'", second);
      if (second && val != -1 && val != 0 && val != 1)
        error ("invalid result argument '%d' to 'fixed", val);
      if (second)
        c = new FixedCall (lit, val);
      else
        c = new FixedCall (lit);
    } else if (!strcmp (keyword, "failed")) {
      if (!first)
        error ("first argument to 'failed' missing");
      if (!parse_int_str (first, lit))
        error ("invalid first argument '%s' to 'failed'", first);
      if (enforce && (!lit || lit == INT_MIN))
        error ("invalid literal '%d 'as argument to 'failed'", lit);
      if (second && !parse_int_str (second, val))
        error ("invalid second argument '%s' to 'failed'", second);
      if (second && val != 0 && val != -1)
        error ("invalid result argument '%d' to 'failed", val);
      if (second)
        c = new FailedCall (lit, val);
      else
        c = new FailedCall (lit);
    } else if (!strcmp (keyword, "conclude")) {
      if (first)
        error ("additional argument '%s' to 'conclude'", first);
      c = new ConcludeCall ();
    } else if (!strcmp (keyword, "freeze")) {
      if (!first)
        error ("argument to 'freeze' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'freeze'", first);
      if (enforce && (!lit || lit == INT_MIN))
        error ("invalid literal %d as argument to 'freeze'", lit);
      if (second)
        error ("additional argument '%s' to 'freeze'", second);
      c = new FreezeCall (lit);
    } else if (!strcmp (keyword, "melt")) {
      if (!first)
        error ("argument to 'melt' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'melt'", first);
      if (enforce && (!lit || lit == INT_MIN))
        error ("invalid literal '%d' as argument to 'melt'", lit);
      if (second)
        error ("additional argument '%s' to 'melt'", second);
      c = new MeltCall (lit);
    } else if (!strcmp (keyword, "frozen")) {
      if (!first)
        error ("first argument to 'frozen' missing");
      if (!parse_int_str (first, lit))
        error ("invalid first argument '%s' to 'frozen'", first);
      if (second && !parse_int_str (second, val))
        error ("invalid second argument '%s' to 'frozen'", second);
      if (second && val != 0 && val != 1)
        error ("invalid result argument '%d' to 'frozen'", val);
      if (second)
        c = new FrozenCall (lit, val);
      else
        c = new FrozenCall (lit);
    } else if (!strcmp (keyword, "dump")) {
      if (first)
        error ("additional argument '%s' to 'dump'", first);
      c = new DumpCall ();
    } else if (!strcmp (keyword, "stats")) {
      if (first)
        error ("additional argument '%s' to 'stats'", first);
      c = new StatsCall ();
    } else if (!strcmp (keyword, "reset")) {
      if (first)
        error ("additional argument '%s' to 'reset'", first);
      c = new ResetCall ();
    } else if (!strcmp (keyword, "trace_proof")) {
      if (!first)
        error ("first argument to 'trace_proof' missing");
      if (second)
        error ("additional argument '%s' to 'trace_proof'", second);
      c = new TraceProofCall (first);
    } else if (!strcmp (keyword, "flush_proof_trace")) {
      if (first)
        error ("additional argument '%s' to 'flush_proof_trace'", first);
      c = new FlushProofTraceCall ();
    } else if (!strcmp (keyword, "close_proof_trace")) {
      if (first)
        error ("additional argument '%s' to 'close_proof_trace'", first);
      c = new CloseProofTraceCall ();
#ifdef MOBICAL_MEMORY
    } else if (!strcmp (keyword, "max_alloc")) {
      if (!mobical.bad_alloc)
        error ("Trace contains a 'max_alloc' call (run without "
               "'--no-bad-alloc')");
      if (!first)
        error ("first argument to 'max_alloc' missing");
      if (!parse_int_str (first, val))
        error ("invalid first argument '%s' to 'max_alloc'", first);
      c = new MaxAllocCall (val);
    } else if (!strcmp (keyword, "leak_alloc")) {
      if (!mobical.leak_alloc)
        error ("Trace contains a 'leak_alloc' call (run without "
               "'--no-leak-alloc')");
      c = new LeakAllocCall ();
#endif
#ifdef MOBICAL_TERMINATE
    } else if (!strcmp (keyword, "terminate")) {
      if (!mobical.terminator)
        error ("Trace contains a 'terminate' call (run without "
               "'--no-terminate')");
      if (!first)
        error ("first argument to 'terminate' missing");
      if (!parse_int_str (first, val))
        error ("invalid first argument '%s' to 'terminate'", first);
      c = new TerminateCall (val);
#endif
    } else if (!strcmp (keyword, "propagate_assumptions")) {
      if (first)
        error ("additional argument to 'propagate_assumptions'");
      c = new PropagateAssumptionsCall ();
    } else if (!strcmp (keyword, "implied")) {
      if (first)
        error ("additional argument to 'implied'");
      c = new ImpliedCall ();
    } else if (!strcmp (keyword, "reset_assumptions")) {
      if (first)
        error ("additional argument to 'reset_assumptions'");
      c = new ResetAssumptionsCall ();
    } else if (!strcmp (keyword, "reset_observed")) {
      if (first)
        error ("additional argument to 'reset_observed'");
      c = new ResetObservedCall ();
    } else if (!strcmp (keyword, "declare_var")) {
      if (first)
        error ("additional argument to 'declare_var'");
      c = new DeclareOneMoreVariableCall ();
    } else
      error ("invalid keyword '%s'", keyword);
    if (enforce && third && !third_argument) {
      error ("invalid third argument '%s' to '%s'", third, keyword);
    }

    // This checks the legal structure of traces described above.
    //
    if (enforce) {
      if (!state && !(c->type & (Call::INIT
#ifdef MOBICAL_MEMORY
                                 | Call::MAXALLOC | Call::LEAKALLOC
#endif
#ifdef MOBICAL_TERMINATE
                                 | Call::TERMINATE
#endif
                                 )))
        error ("first call has to be an 'init', 'max_alloc', 'leak_alloc'"
               " or 'terminate' call");

      if (state == Call::RESET)
        error ("'%s' after 'reset'", c->keyword ());

      if (adding && c->type != adding && c->type != Call::RESET &&
          ((adding == Call::ADD && c->type != Call::RESIZE) ||
           (adding == Call::CONSTRAIN && c->type != Call::FIXED)))
        error ("'%s' after '%s %d' without '%s 0'", c->keyword (),
               prev->keyword (), prev->arg, prev->keyword ());

      uint64_t new_state = state;

      switch ((uint64_t) c->type) {

      case Call::INIT:
        if (state)
          error ("invalid second 'init' call");
        new_state = Call::CONFIG;
        break;

      case Call::SET:
      case Call::CONFIGURE:
        if (!solved && state == Call::BEFORE) {
          assert (before_trigger);
          error ("'%s' can only be called after 'init' before '%s %d'",
                 c->keyword (), before_trigger->keyword (),
                 before_trigger->arg);
        } else if (state != Call::CONFIG)
          error ("'%s' can only be called right after 'init'",
                 c->keyword ());
        assert (new_state == Call::CONFIG);
        break;

      case Call::ADD:
      case Call::ASSUME:
        if (state != Call::BEFORE)
          before_trigger = c;
        new_state = Call::BEFORE;
        break;

      case Call::LEMMA:
      case Call::FORCE:
      case Call::DECIDE:
        if (!connected)
          error ("'%s' can only be called after 'connect'", c->keyword ());
        new_state = Call::DURING;
        break;

      case Call::OBSERVE:
      case Call::UNOBSERVE:
      case Call::RESET_OBSERVED:
        if (!connected)
          error ("'%s' can only be called after 'connect'", c->keyword ());
        new_state = c->type;
        break;

      case Call::VAL:
      case Call::FLIP:
      case Call::FLIPPABLE:
      case Call::FAILED:
      case Call::CONCLUDE:
        if (!solved && (state == Call::CONFIG || state == Call::BEFORE))
          error ("'%s' can only be called after 'solve'", c->keyword ());
        if (solved && state == Call::BEFORE) {
          assert (before_trigger);
          error ("'%s' only valid after last 'solve' and before '%s %d'",
                 c->keyword (), before_trigger->keyword (),
                 before_trigger->arg);
        }
        assert (state == Call::SOLVE || state == Call::SIMPLIFY ||
                state == Call::LOOKAHEAD || state == Call::CUBING ||
                state == Call::PROPAGATE || state == Call::OBSERVE ||
                state == Call::DURING || state == Call::AFTER);
        new_state = Call::AFTER;
        break;

      case Call::DISCONNECT:
        if (!connected)
          error ("'%s' can only be called after 'connect'", c->keyword ());
        connected = false;
        new_state = c->type;
        break;

      case Call::CONNECT:
        if (connected)
          error ("call 'disconnect' before call 'connect' again");
        connected = true;
        new_state = c->type;
        break;

      case Call::SOLVE:
      case Call::SIMPLIFY:
      case Call::LOOKAHEAD:
      case Call::CUBING:
      case Call::PROPAGATE:
      case Call::RESET:
        new_state = c->type;
        break;

      default:
        break;
      }

      state = new_state;
      prev = c;
    }

#ifdef LOGGING
    if (!trace.calls.empty () && trace.calls.back ()->type == Call::INIT &&
        mobical.add_set_log_to_true)
      trace.push_back (new SetCall ("log", 1));
#endif

    if (c && mobical.add_dump_before_solve && c->process_type ())
      trace.push_back (new DumpCall ());

    trace.push_back (c);

    if (c && mobical.add_stats_after_solve && c->process_type ())
      trace.push_back (new StatsCall ());

    lineno++;
  }
  if (adding) {
    assert (prev);
    error ("EOF after '%s %d' without '%s 0'", prev->keyword (), prev->arg,
           prev->keyword ());
  }
}

/*------------------------------------------------------------------------*/

bool Mobical::is_unsigned_str (const char *str) {
  const char *p = str;
  if (!*p)
    return false;
  if (!isdigit (*p++))
    return false;
  while (isdigit (*p))
    p++;
  return !*p;
}

uint64_t Mobical::parse_seed (const char *str) {
  const uint64_t max = ~(uint64_t) 0;
  uint64_t res = 0;
  for (const char *p = str; *p; p++) {
    if (max / 10 < res)
      die ("invalid seed '%s' (too many digits)", str);
    res *= 10;
    assert (isdigit (*p));
    unsigned digit = *p - '0';
    if (max - digit < res)
      die ("invalid seed '%s' (too large)", str);
    res += digit;
  }
  return res;
}

/*------------------------------------------------------------------------*/

void Mobical::header () {
  terminal.blue ();
  cerr << "calls";
  terminal.magenta ();
  cerr << " vars";
  terminal.yellow ();
  cerr << " clauses";
  terminal.normal ();
}

/*------------------------------------------------------------------------*/

extern "C" {
#include <sys/mman.h>
}

// https://github.com/libressl/portable/issues/24\#issuecomment-50435773
// The usage of MAP_ANONYMOUS vs MAP_ANON depends on the actual system
#if !defined(MAP_ANONYMOUS) && defined(MAP_ANON)
#define MAP_ANONYMOUS MAP_ANON
#elif !defined(MAP_ANONYMOUS)
#error "System does not support mapping anonymous pages?"
#endif

Mobical::Mobical () {
  const int prot = PROT_READ | PROT_WRITE;
  const int flags = MAP_ANONYMOUS | MAP_SHARED;
  shared = (Shared *) mmap (0, sizeof *shared, prot, flags, -1, 0);
}

Mobical::~Mobical () {
  if (shared)
    munmap (shared, sizeof *shared);
  delete mock_pointer;
  delete replay_pointer;
}

void Mobical::catch_signal (int) {
  if ((terminal && (mode & RANDOM)) || shrinking || running)
    cerr << endl;
  terminal.reset ();
  if (Trace::executed && !Trace::failed && !Trace::ok)
    assert (mode & (INPUT | SEED)), Trace::failed = 1;
  print_statistics ();
}

/*------------------------------------------------------------------------*/

int Mobical::main (int argc, char **argv) {
  // First parse command line options and determine mode.
  //
  const char *seed_str = 0;
  const char *input_path = 0;
  const char *output_path = 0;

  int64_t limit = -1;
  int64_t bug_limit = -1;

  int summary = -1;

  // Error message in 'die' also uses colors.
  //
  for (int i = 1; i < argc; i++)
    if (is_color_option (argv[i]))
      tout.force_colors (), terr.force_colors ();
    else if (is_no_color_option (argv[i]))
      terminal.force_no_colors ();
    else if (!strcmp (argv[i], "--no-terminal"))
      terminal.disable ();

  for (int i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h")) {
      printf (USAGE, DEFAULT_TIME_LIMIT, DEFAULT_SPACE_LIMIT);
      exit (0);
    } else if (!strcmp (argv[i], "--version"))
      puts (version ()), exit (0);
    else if (!strcmp (argv[i], "--build")) {
      tout.disable ();
      Solver::build (stdout, "");
      exit (0);
    } else if (!strcmp (argv[i], "-v") || !strcmp (argv[i], "--verbose"))
      verbose = true;
    else if (!strcmp (argv[i], "-q") || !strcmp (argv[i], "--quiet")) {
      terminal.disable ();
      quiet = true;
    } else if (is_color_option (argv[i]))
      ;
    else if (is_no_color_option (argv[i]))
      ;
    else if (!strcmp (argv[i], "--no-terminal"))
      assert (!terminal);
    else if (!strcmp (argv[i], "--do-not-execute"))
      donot.execute = true;
    else if (!strcmp (argv[i], "--do-not-fork"))
      donot.fork = true;
    else if (!strcmp (argv[i], "--do-not-enforce-contracts"))
      donot.enforce = true;
    else if (!strcmp (argv[i], "--no-seeds"))
      donot.seeds = true;
    else if (!strcmp (argv[i], "--no-summary"))
      summary = 0;
    else if (!strcmp (argv[i], "--summary"))
      summary = 1;
    else if (!strcmp (argv[i], "--no-mock"))
      donot.mock_propagator = true;
    else if (!strcmp (argv[i], "--no-mock-relaxed")) {
      donot.mock_propagator = true;
      donot.replay_strict = true;
    } else if (!strcmp (argv[i], "--do-not-shrink") ||
               !strcmp (argv[i], "--do-not-shrink-at-all"))
      donot.shrink.atall = true;
    else if (!strcmp (argv[i], "--do-not-add-options") ||
             !strcmp (argv[i], "--do-not-add-options-before-shrinking"))
      donot.add = true;
    else if (!strcmp (argv[i], "--do-not-shrink-phases"))
      donot.shrink.phases = true;
    else if (!strcmp (argv[i], "--do-not-shrink-clauses"))
      donot.shrink.clauses = true;
    else if (!strcmp (argv[i], "--do-not-shrink-lemmas"))
      donot.shrink.lemmas = true;
    else if (!strcmp (argv[i], "--do-not-shrink-propagator"))
      donot.shrink.propagator = true;
    else if (!strcmp (argv[i], "--do-not-shrink-literals"))
      donot.shrink.literals = true;
    else if (!strcmp (argv[i], "--do-not-shrink-basic") ||
             !strcmp (argv[i], "--do-not-shrink-basic-calls"))
      donot.shrink.basic = true;
    else if (!strcmp (argv[i], "--do-not-shrink-options"))
      donot.shrink.options = true;
    else if (!strcmp (argv[i], "--do-not-disable") ||
             !strcmp (argv[i], "--do-not-disable-options"))
      donot.disable = true;
    else if (!strcmp (argv[i], "--do-not-shrink-variables"))
      donot.map = true;
    else if (!strcmp (argv[i], "--do-not-reduce") ||
             !strcmp (argv[i], "--do-not-reduce-values") ||
             !strcmp (argv[i], "--do-not-reduce-option-values"))
      donot.reduce = true;
    else if (!strcmp (argv[i], "--tiny"))
      force.size = TINY;
    else if (!strcmp (argv[i], "--small"))
      force.size = SMALL;
    else if (!strcmp (argv[i], "--medium"))
      force.size = MEDIUM;
    else if (!strcmp (argv[i], "--big"))
      force.size = BIG;
    else if (!strcmp (argv[i], "-l") || !strcmp (argv[i], "--log")) {
      add_set_log_to_true = true;
    } else if (!strcmp (argv[i], "-d") || !strcmp (argv[i], "--dump")) {
      add_dump_before_solve = true;
    } else if (!strcmp (argv[i], "-s") || !strcmp (argv[i], "--stats")) {
      add_stats_after_solve = true;
    } else if (!strcmp (argv[i], "-p") || !strcmp (argv[i], "--plain")) {
      add_plain_after_options = true;
    } else if (!strcmp (argv[i], "-L")) {
      if (limit >= 0)
        die ("multiple '-L' options (try '-h')");
      if (++i == argc)
        die ("argument to '-L' missing (try '-h')");
      if (!is_unsigned_str (argv[i]) || (limit = atol (argv[i])) < 0)
        die ("invalid argument '%s' to '-L' (try '-h')", argv[i]);
    } else if (argv[i][0] == '-' && argv[i][1] == 'L') {
      if (limit >= 0)
        die ("multiple '-L' options (try '-h')");
      if (!is_unsigned_str (argv[i] + 2) ||
          (limit = atol (argv[i] + 2)) < 0)
        die ("invalid argument in '%s' (try '-h')", argv[i]);
    } else if (!strcmp (argv[i], "-X")) {
      if (bug_limit >= 0)
        die ("multiple '-X' options (try '-h')");
      if (++i == argc)
        die ("argument to '-X' missing (try '-h')");
      if (!is_unsigned_str (argv[i]) || (bug_limit = atol (argv[i])) < 0)
        die ("invalid argument '%s' to '-X' (try '-h')", argv[i]);
    } else if (argv[i][0] == '-' && argv[i][1] == 'X') {
      if (bug_limit >= 0)
        die ("multiple '-X' options (try '-h')");
      if (!is_unsigned_str (argv[i] + 2) ||
          (bug_limit = atol (argv[i] + 2)) < 0)
        die ("invalid argument in '%s' (try '-h')", argv[i]);
    } else if (!strcmp (argv[i], "-F")) {
      if (++i == argc)
        die ("argument to '-F' missing (try '-h')");
      string parse_name;
      int parse_value;
      if (!mopts.parse_long_option (argv[i], parse_name, parse_value))
        die ("invalid argument '%s' to '-F' (try '-h')", argv[i]);
      mopts.set (parse_name.c_str (), parse_value);
    } else if (argv[i][0] == '-' && argv[i][1] == 'F') {
      string parse_name;
      int parse_value;
      if (!mopts.parse_long_option (argv[i] + 2, parse_name, parse_value))
        die ("invalid argument '%s' to '-F' (try '-h')", argv[i]);
      mopts.set (parse_name.c_str (), parse_value);
    } else if (!strcmp (argv[i], "--time")) {
      if (++i == argc)
        die ("argument to '--time' missing (try '-h')");
      if (!is_unsigned_str (argv[i]) || (time_limit = atol (argv[i])) < 0 ||
          time_limit > 1e9)
        die ("invalid argument '%s' to '--time' (try '-h')", argv[i]);
    } else if (!strcmp (argv[i], "--space")) {
      if (++i == argc)
        die ("argument to '--space' missing (try '-h')");
      if (!is_unsigned_str (argv[i]) ||
          (space_limit = atol (argv[i])) < 0 || space_limit > 1e9)
        die ("invalid argument '%s' to '--space' (try '-h')", argv[i]);
#ifdef MOBICAL_MEMORY
    } else if (!strcmp (argv[i], "--no-bad-alloc")) {
      bad_alloc = false;
    } else if (!strcmp (argv[i], "--no-leak-alloc")) {
      leak_alloc = false;
#endif
#ifdef MOBICAL_TERMINATE
    } else if (!strcmp (argv[i], "--no-terminator")) {
      terminator = false;
#endif
    } else if (!strcmp (argv[i], "--do-not-ignore-resource-limits")) {
      donot.ignore_resource_limits = true;
    } else if (argv[i][0] == '-' && is_unsigned_str (argv[i] + 1)) {
      force.phases = atoi (argv[i] + 1);
      if (force.phases < 0)
        die ("invalid number of phases '%s'", argv[i]);
    } else if (argv[i][0] == '-' && argv[i][1])
      die ("invalid option '%s' (try '-h')", argv[i]);
    else if (is_unsigned_str (argv[i])) {
      if (seed_str)
        die ("can not handle multiple seeds '%s' and '%s' (try '-h')",
             seed_str, argv[i]);
      if (input_path)
        die ("can not combine input trace '%s' and seed '%s' (try '-h')",
             input_path, argv[i]);
      seed_str = argv[i];
    } else if (output_path) {
      assert (input_path);
      die ("too many trace files specified: '%s', '%s' and '%s' (try "
           "'-h')",
           input_path, output_path, argv[i]);
    } else if (input_path) {
      if (seed_str)
        die ("seed '%s' with two output files '%s' and '%s' ", seed_str,
             input_path, argv[i]);
      if (strcmp (input_path, "-") && !strcmp (input_path, argv[i]))
        die ("input '%s' and output '%s' are the same", input_path,
             argv[i]);
      output_path = argv[i];
    } else {
      if (!seed_str && strcmp (argv[i], "-") && !File::exists (argv[i]))
        die ("can not access input trace '%s' (try '-h')", argv[i]);
      input_path = argv[i];
    }
  }

  /*----------------------------------------------------------------------*/

  // If a seed and a file (in that order) are specified the file is
  // actually not an input file but an output file.  To streamline the
  // code below swap input and output here.
  //
  if (input_path && seed_str) {
    assert (!output_path);
    output_path = input_path;
    input_path = 0;
  }

  if (output_path && !File::writable (output_path))
    die ("can not write output trace '%s' (try '-h')", output_path);

  /*----------------------------------------------------------------------*/

  // Check illegal combinations of options.

  if (input_path && donot.seeds)
    die ("can not use '--no-seeds' while specifying input '%s' explicitly",
         input_path);

  if (input_path && limit >= 0)
    die ("can not combine '-L' and input '%s'", input_path);

  if (output_path && limit >= 0)
    die ("can not combine '-L' and output '%s'", output_path);

  if (input_path && bug_limit >= 0)
    die ("can not combine '-X' and input '%s'", input_path);

  if (output_path && bug_limit >= 0)
    die ("can not combine '-X' and output '%s'", output_path);

  if (!output_path && donot.execute)
    die ("can not use '--do-no-execute' without '<output>'");

  if (!input_path && donot.mock_propagator)
    die ("can not use '--no-mock' without '<input>'");

  if (output_path && donot.mock_propagator)
    die ("can not use '--no-mock' with '<output>'");

  if (!input_path && donot.enforce)
    die ("can not use '--do-not-enforce-contracts' without '<input>'");

  if (output_path && donot.enforce)
    die ("can not use '--do-not-enforce-contracts' "
         "with both '<input>' and '<output>'");

  /*----------------------------------------------------------------------*/

  // Set mode.

  if (limit >= 0)
    mode = RANDOM;
  else {
    if (seed_str || input_path)
      mode = 0;
    else
      mode = RANDOM;
    if (seed_str)
      mode |= SEED;
    if (input_path)
      mode |= INPUT;
    if (output_path)
      mode |= OUTPUT;
  }
  check_mode_valid ();

  if (summary == 1)
    donot.summary = false;
  else if (summary == 0)
    donot.summary = true;
  else if (mode & RANDOM)
    donot.summary = false;
  else
    donot.summary = true;

  /*----------------------------------------------------------------------*/

  if (quiet)
    goto END_OF_BANNER_AND_OPTIONS;

  // Print banner.

  prefix ();
  terminal.magenta (1);
  fputs ("Model Based Tester for the CaDiCaL SAT Solver Library\n", stderr);
  terminal.normal ();
  prefix ();
  terminal.magenta (1);
  fprintf (stderr, "%s\n", copyright ());
  terminal.normal ();
  prefix ();
  terminal.magenta (1);
  fprintf (stderr, "%s\n", authors ());
  terminal.normal ();
  prefix ();
  terminal.magenta (1);
  fprintf (stderr, "%s\n", affiliations ());
  terminal.normal ();
  empty_line ();
  Solver::build (stderr, prefix_string ());
  terminal.normal ();
  empty_line ();

  /*----------------------------------------------------------------------*/

  // Print resource limits (per executed trace).

  prefix ();
  if (mobical.donot.fork)
    cerr << "not using any time limit due to '--do-not-fork'";
  else if (time_limit == DEFAULT_TIME_LIMIT)
    cerr << "using default time limit of " << time_limit << " seconds";
  else if (time_limit)
    cerr << "using explicitly specified time limit of " << time_limit
         << " seconds";
  else
    cerr << "explicitly using no time limit";

  cerr << endl << flush;

  prefix ();
  if (mobical.donot.fork)
    cerr << "not using any space limit due to '--do-not-fork'";
  else if (space_limit == DEFAULT_SPACE_LIMIT)
    cerr << "using default space limit of " << space_limit << " MB";
  else if (space_limit)
    cerr << "using explicitly specified space limit of " << space_limit
         << " MB";
  else
    cerr << "explicitly using no space limit";

  cerr << endl << flush;

  if (mobical.add_plain_after_options) {
    prefix ();
    cerr << "generating only plain instances (--plain)" << endl << flush;
  }
#ifdef MOBICAL_MEMORY
  if (mobical.bad_alloc && mobical.leak_alloc) {
    prefix ();
    cerr << "fuzzing memory allocation limits and leaks" << endl;
  } else if (mobical.bad_alloc) {
    prefix ();
    cerr << "fuzzing memory allocation limits" << endl;
  } else if (mobical.leak_alloc) {
    prefix ();
    cerr << "fuzzing memory leaks" << endl;
  }
#endif
#ifdef MOBICAL_TERMINATE
  if (mobical.terminator) {
    prefix ();
    cerr << "generate terminate limits" << endl;
  }
#endif

  /*----------------------------------------------------------------------*/

  // Report mode.

  if (mode & RANDOM) {
    prefix ();
    if (limit >= 0) {
      cerr << "randomly generating " << limit << " traces";
      if (bug_limit >= 0)
        cerr << " or until " << bug_limit << " failed";
      cerr << endl;
    } else {
      cerr << "randomly generating traces";
      if (bug_limit >= 0)
        cerr << " until " << bug_limit << " failed";
      if (terminal) {
        terminal.magenta ();
        cerr << " (press ";
        terminal.blue ();
        cerr << "'<control-c>'";
        terminal.magenta ();
        cerr << " to stop)";
        terminal.normal ();
      }
      cerr << endl;
    }
    empty_line ();
  }
  if (mode & SEED) {
    assert (seed_str);
    prefix ();
    cerr << "generating single trace from seed '" << seed_str << '\''
         << endl;
  }
  if (mode & INPUT) {
    assert (input_path);
    prefix ();
    cerr << "reading single trace from input '" << input_path << '\''
         << endl;
  }
  if (mode & OUTPUT) {
    assert (output_path);
    prefix ();
    cerr << "writing " << (donot.shrink.atall ? "original" : "shrunken")
         << " trace to output '" << output_path << '\'' << endl;
  }
  cerr << flush;

END_OF_BANNER_AND_OPTIONS:

  /*----------------------------------------------------------------------*/

  Signal::set (this);

  int res = 0;

  if (mode & (SEED | INPUT)) { // trace given through input or seed

    if (!quiet) {
      prefix ();
      cerr << right << setw (58) << "";
      header ();
      cerr << endl;
      hline ();
    }

    Trace trace;

    if (seed_str) { // seed

      uint64_t seed = parse_seed (seed_str);

      if (quiet) {
        cerr << "seed: ";
        cerr << setfill ('0') << right << setw (20) << seed;
        cerr << endl << flush;
      } else {
        prefix ();
        cerr << left << setw (13) << "seed:";
        assert (is_unsigned_str (seed_str));
        terminal.green ();
        cerr << setfill ('0') << right << setw (20) << seed;
        terminal.normal ();
        cerr << setfill (' ') << setw (24) << "";
      }

      Trace::generated++;

      trace.generate (0, seed);

    } else { // input

      Reader reader (*this, trace, input_path);
      reader.parse ();

      if (!quiet) {
        prefix ();
        cerr << left << setw (13) << "input: ";
        assert (input_path);
        cerr << left << setw (44) << input_path;
      }
    }

    if (!quiet) {
      cerr << ' ';
      summarize (trace);
      cerr << endl << flush;
    }

    if (output_path) {

      if (!donot.execute) {

        res = trace.fork_and_execute ();
        if (res) {
          res = trace.fork_and_execute ();
          if (!res)
            spurious++;
        }

        if (res) {

          if (!donot.shrink.atall) {

            if (!quiet)
              terminal.cursor (false);

            Trace::failed++;
            trace.shrink (res); // shrink
            if (!quiet) {
              if (!verbose && !terminal)
                cerr << endl;
              else
                terminal.erase_line_if_connected_otherwise_new_line ();
            }
          }

        } else
          Trace::ok++;
      }

      if (!quiet) {
        prefix ();
        cerr << left << setw (13) << "output:";
      }

      trace.write_path (output_path, res); // output

      if (!quiet) {
        if (res)
          terminal.red (true);
        cerr << left << setw (44);
        if (!strcmp (output_path, "-"))
          cerr << "<stdout>";
        else
          cerr << output_path;
        terminal.normal ();
        cerr << ' ';
        summarize (trace);
        cerr << endl << flush;
      }

    } else {
      trace.execute (); // execute
      Trace::ok++;
    }

  } else { // otherwise generate random traces forever

    Random random; // initialized by time and machine id

    if (limit < 0)
      limit = LONG_MAX;
    if (bug_limit < 0)
      bug_limit = LONG_MAX;

    if (seed_str) {
      uint64_t seed = parse_seed (seed_str);
      if (!quiet)
        terminal.green ();
      random = seed;
    }

    if (quiet) {
      cerr << "seed: ";
      cerr << setfill ('0') << right << setw (20) << random.seed ();
      cerr << endl << flush;
    } else if (!quiet) {
      prefix ();
      cerr << "start seed ";
      terminal.green ();
      cerr << random.seed ();
      terminal.normal ();
      cerr << endl;
      empty_line ();

      prefix ();
      cerr << left << setw (14) << "count";
      terminal.green ();
      cerr << "seed";
      terminal.black ();
      cerr << '/';
      terminal.red ();
      cerr << "buggy";
      terminal.black ();
      cerr << '/';
      terminal.yellow ();
      cerr << "reducing";
      terminal.black ();
      cerr << '/';
      terminal.red (true);
      cerr << "reduced";
      cerr << left << setw (17) << "";
      header ();
      cerr << endl;
      hline ();

      terminal.cursor (false);
    }

    for (traces = 1; traces <= limit; traces++) {
      if (Trace::failed >= bug_limit)
        break;

      if (!quiet && !donot.seeds) {
        prefix ();
        cerr << ' ' << left << setw (15) << traces << ' ';
        terminal.green ();
        cerr << setfill ('0') << right << setw (20) << random.seed ();
        terminal.normal ();
        cerr << setfill (' ') << flush;
      }

      Trace trace;
      Trace::generated++;
      trace.generate (traces, random.seed ()); // generate

      if (!quiet && !donot.seeds) {
        cerr << setw (21) << "";
        summarize (trace);
        terminal.erase_until_end_of_line ();
        cerr << flush;
      }

      running = true;
      res = trace.fork_and_execute (); // execute
      if (res) {
        res = trace.fork_and_execute ();
        if (!res)
          spurious++;
      }
      if (res)
        Trace::failed++;
      else
        Trace::ok++;

      if (!quiet) {
        if (!donot.seeds && limit != traces)
          terminal.erase_line_if_connected_otherwise_new_line ();
        else if (!donot.seeds && limit == traces)
          cerr << endl << flush;
      }

      if (res) { // failed

        if (!quiet) {
          prefix ();
          cerr << ' ' << left << setw (11) << traces << ' ';
          terminal.red ();
        }
        trace.write_prefixed_seed ("bug", res); // output
        if (quiet) {
          cerr << endl << flush;
        } else {
          terminal.normal ();
          cerr << setw (15) << "";
          summarize (trace);
          if (terminal)
            cerr << endl << flush;
        }

        running = false;

        if (!donot.shrink.atall) {
          trace.shrink (res); // shrink
          if (quiet) {
            ; //  TODO remove: cerr << endl << flush;
          } else {
            if (!terminal && !verbose)
              cerr << endl;
            else
              terminal.erase_line_if_connected_otherwise_new_line ();
          }
        }

        if (!quiet) {
          prefix ();
          cerr << ' ' << left << setw (11) << traces << ' ';
          terminal.red (true);
        }

        trace.write_prefixed_seed ("red", res); // output

        if (quiet) {
          cerr << endl << flush;
        } else {
          terminal.normal ();
          cerr << setw (15) << "";
          summarize (trace, true);
          cerr << endl << flush;
        }
      }

      random.next ();
    }
  }

  Signal::reset ();

  terminal.reset ();
  print_statistics ();

  return Trace::failed > 0;
}

/*------------------------------------------------------------------------*/
} // namespace CaDiCaL
/*------------------------------------------------------------------------*/

int main (int argc, char **argv) {
#ifdef MOBICAL_MEMORY
  // Disable buffers as they are otherwise detected as memory leak
  setvbuf (stdout, NULL, _IONBF, 0);
  setvbuf (stderr, NULL, _IONBF, 0);
  setvbuf (stdin, NULL, _IONBF, 0);
#endif
  return CaDiCaL::mobical.main (argc, argv);
}
