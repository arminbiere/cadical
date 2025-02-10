/*------------------------------------------------------------------------*/
/* Copyright (C) 2018-2021 Armin Biere, Johannes Kepler University Linz   */
/* Copyright (C) 2020-2021 Mathias Fleury, Johannes Kepler University Linz*/
/* Copyright (c) 2020-2021 Nils Froleyks, Johannes Kepler University Linz */
/* Copyright (C) 2022-2024 Katalin Fazekas, Technical University of Vienna*/
/* Copyright (C) 2021-2024 Armin Biere, University of Freiburg            */
/* Copyright (C) 2021-2023 Mathias Fleury, University of Freiburg         */
/* Copyright (C) 2023-2024 Florian Pollitt, University of Freiburg        */
/* Copyright (C) 2024-2024 Tobias Faller Fleury, University of Freiburg   */
/*------------------------------------------------------------------------*/

// Model Based Tester for the CaDiCaL SAT Solver Library.

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
"  -v                increase verbosity\n"
"  --colors          force colors for both '<stdout>' and '<stderr>'\n"
"  --no-colors       disable colors if '<stderr>' is connected to terminal\n"
"  --no-terminal     assume '<stderr>' is not connected to terminal\n"
"  --no-seeds        do not print seeds in random mode\n"
"\n"
"  -<n>              specify the number of solving phases explicitly\n"
"  --time <seconds>  set time limit per trace (none=0, default=%d)\n"
"  --space <MB>      set space limit (none=0, default=%d)\n"
"  --bad-alloc       generate failing memory allocations, monitor for crashes\n"
"  --leak-alloc      generate failing memory allocations, monitor for leaks\n"
"\n"
"  --do-not-ignore-resource-limits  consider out-of-time or memory as error\n"
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
"In order to let the test exectue '<r>' runs (starting from '<seed>') use:\n"
"\n"
"  -L[ ]<r>          execute '<r>' runs\n"
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
  bool add = false;        // add all options before shrinking    'a'
  struct {                 //
    bool atall = false;    // do not shrink anything              's'
    bool phases = false;   // shrink complete incremental solving 'p'
    bool clauses = false;  // shrink full clauses                 'c'
    bool literals = false; // shrink literals which shrinks       'l'
    bool basic = false;    // shrink other basic calls            'b'
    bool options = false;  // shrink option calls                 'o'
  } shrink;                //
  bool disable = false;    // try to eagerly disable all options  'd'
  bool map = false;        // do not map variable indices         'm'
  bool reduce = false;     // reduce option values                'r'
  bool execute = false;    // do not execute trace
  bool fork = false;       // do not fork sub-process
  bool enforce = false;    // do not enforce contracts on read trace
  bool seeds = false;
  bool ignore_resource_limits = false;
};

/*------------------------------------------------------------------------*/

struct Shared {
  int64_t solved;
  int64_t incremental;
  int64_t unsat;
  int64_t sat;
  int64_t memout;
  int64_t timeout;
  int64_t oom;

#ifdef MOBICAL_MEMORY
#define MOBICAL_MEMORY_STACK_COUNT 64
#define MOBICAL_MEMORY_LEAK_COUNT (1024 * 64)
  struct {
    size_t debug_filter_index;
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
};

/*------------------------------------------------------------------------*/

class MockPropagator : public ExternalPropagator,
                       public FixedAssignmentListener {
private:
  Solver *s = 0;

  // MockPropagator parameters
  size_t lemma_per_cb = 2;
  bool logging = false;

  struct ExternalLemma {
    size_t id;
    size_t add_count;
    size_t size;
    size_t next;

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

  // The reasons of present external propagations
  std::map<int, int> reason_map;
  // The external propagations that are currently unassigned
  std::set<int> unassigned_reasons;

  // Next lemma to add
  size_t add_lemma_idx = 0;

  // Forced lemme addition (falsified lemma in model)
  bool must_add_clause = false;
  size_t must_add_idx;
  // Next decision to make
  size_t decision_loc = 0;

  // Observed variables and their current assignments
  std::set<int> observed_variables;
  std::vector<int> new_observed_variables;
  std::deque<std::vector<int>> observed_trail;

  // Helpers
  size_t added_lemma_count = 0;
  size_t nof_clauses = 0;
  std::vector<int> clause;
  bool new_ovars = false;

  size_t add_new_lemma (bool forgettable) {
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

  // Helper to print very verbose log during debugging

#ifdef LOGGING
#define MLOG(str) \
  do { \
    if (logging) \
      std::cout << "[mock-propagator] " << str; \
  } while (false)
#define MLOGC(str) \
  do { \
    if (logging) \
      std::cout << str; \
  } while (false)
#else
#define MLOG(str) \
  do { \
  } while (false)
#define MLOGC(str) \
  do { \
  } while (false)
#endif

public:
  // It is public, so it can be shared easily between different propagators
  std::vector<int> observed_fixed;

  MockPropagator (Solver *solver, bool with_logging = false) {
    observed_trail.push_back (std::vector<int> ());
    s = solver;
    logging = logging || with_logging;
  }

  ~MockPropagator () {
    for (auto l : external_lemmas)
      delete[] l->literals, delete l;

    s = 0;
    reason_map.clear ();
    unassigned_reasons.clear ();

    observed_variables.clear ();
    new_observed_variables.clear ();
    observed_trail.clear ();

    observed_fixed.clear ();
  }

  /*-----------------functions for mobical -----------------------------*/
  void push_lemma_lit (int lit) {

    if (lit)
      clause.push_back (lit);
    else {
      nof_clauses++;

      MLOG ("push lemma to position " << external_lemmas.size () << ": ");
      for (auto const &l : clause) {
        (void) l;
        MLOGC (l << " ");
      }
      MLOGC ("0" << std::endl);

      add_new_lemma (true);
      clause.clear ();
    }
  }

  void add_observed_lit (int lit) {
    // Zero lit indicates that the new observed variables start here
    if (!lit) {
      assert (!new_ovars);
      new_ovars = true;
      return;
    }

    if (!new_ovars) {
      if (!s->is_witness (abs (lit))) {
        s->add_observed_var (abs (lit));
        observed_variables.insert (abs (lit));
      }
    } else {
      new_observed_variables.push_back (abs (lit));
    }
  }

  int add_new_observed_var () {
    for (std::vector<int>::iterator it = new_observed_variables.begin ();
         it != new_observed_variables.end (); ++it) {
      int lit = *it;
      if (s->is_witness (lit))
        continue;
      new_observed_variables.erase (it);
      observed_variables.insert (lit);

      s->add_observed_var (lit);
      return lit;
    }
    return 0;
  }

  int remove_new_observed_var () {
    // TODO: check out red-02744449867227930989.trace
    return 0;
  }

  bool is_observed_now (int lit) {
    return (observed_variables.find (abs (lit)) !=
            observed_variables.end ());
  }

  bool compare_trails () {
#ifndef NDEBUG
    std::set<int> etrail = {}; // Trail of the solver
    std::set<int> efixed = {}; // Fixed assignments in the solver

    std::set<int> otrail = {}; // Observed trail
    std::set<int> ofixed = {}; // Observed fixed assignments

    size_t idx = 0;

    // 1. Collect merged/eliminated variables in case there are:
    std::vector<int> eq_class = {};
    // can be an expensive call, avoid if possible
    bool is_merger = s->internal->get_merged_literals (eq_class);
    if (is_merger) {
      for (const auto &elit : eq_class) {
        if (is_observed_now (elit)) {
          etrail.insert (elit);
        }
      }
      idx++; // trail[0] is processed already
    }

    // 2. Collect all other variables from trail
    for (; idx < s->internal->trail.size (); idx++) {
      int ilit = s->internal->trail[idx];
      int elit = s->internal->externalize (ilit);
      if (is_observed_now (elit)) {
        etrail.insert (elit);
      }
    }

    for (const auto &level : observed_trail) {
      for (const auto elit : level) {
        if (is_observed_now (elit)) {
          // There can be duplicate assignments due to fixed variables
          // so assert (otrail_inserted == otrail.size()) will not work.
          assert (otrail.count (elit) == 0 ||
                  std::find (observed_fixed.begin (), observed_fixed.end (),
                             elit) != observed_fixed.end ());

          otrail.insert (elit);
        }
      }
    }
#ifdef LOGGING
    if (etrail.size () != otrail.size ()) {
      MLOG ("etrail: ");
      for (auto const &lit : etrail)
        MLOGC (lit << " ");
      MLOGC (std::endl);
      MLOG ("otrail: ");
      for (auto const &lit : otrail)
        MLOGC (lit << " ");
      MLOGC (std::endl);
    }
#endif
    assert (etrail.size () == otrail.size ());

    assert (etrail == otrail);

#endif
    return true;
  }
  /*-----------------functions for mobical ends ------------------------*/

  /*------------------ FixedAssignmentListener functions
   * ---------------------*/
  void notify_fixed_assignment (int lit) override {
    MLOG ("notify_fixed_assignment: "
          << lit << " (current level: " << observed_trail.size () - 1
          << ", current fixed count: " << observed_fixed.size () << ")"
          << std::endl);

    assert (std::find (observed_fixed.begin (), observed_fixed.end (),
                       lit) == observed_fixed.end ());
    observed_fixed.push_back (lit);
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
    MLOGC ("found: " << fixed_lits.size () << " fixed literals"
                     << std::endl);
    add_prev_fixed (fixed_lits);
    fixed_lits.clear ();
#endif
  }

  /* ---------------- FixedAssignmentListener functions end
   * ------------------*/

  /* -------------------- ExternalPropagator functions -----------------*/

  bool cb_check_found_model (const std::vector<int> &model) override {
    MLOG ("cb_check_found_model (" << model.size () << ") returns: ");

    // Model reconstruction can change the assignments of certain variables,
    // but the internal trail of the solver and the propagator should be
    // still in synchron.
    assert (compare_trails ());

    for (const auto lemma : external_lemmas) {
      bool satisfied = false;

      for (const auto lit : *lemma) {
        if (!lit)
          continue; // eoc

        auto search = std::find (model.begin (), model.end (), lit);
        if (search != model.end ()) {
          satisfied = true;
          break;
        } else {
          // if not satisfied, it must be falsified.
          search = std::find (model.begin (), model.end (), -lit);
          assert (search != model.end ());
        }
      }

      if (!satisfied) {
        assert (lemma->add_count == 0 || lemma->forgettable);

        must_add_clause = true;
        must_add_idx = lemma->id;

        MLOGC ("false (external clause  "
               << lemma->id << "/" << external_lemmas.size ()
               << " is not satisfied: (forgettable: " << lemma->forgettable
               << ", size: " << lemma->size << "): ");
        for (auto const &l : *lemma) {
          MLOGC (l << " ");
          (void) l;
        }
        MLOGC (std::endl);

        return false;
      }
    }

    MLOGC ("true" << std::endl);

    return true;
  }

  // Before finalizing the new ipasir-up
  bool cb_has_external_clause () {
    bool forgettable = true;
    return cb_has_external_clause (forgettable);
  }

  bool cb_has_external_clause (bool &forgettable) override {
    MLOG ("cb_has_external_clause returns: ");

    assert (compare_trails ());

    forgettable = false;

    if (external_lemmas.empty ()) {
      MLOGC ("false (there are no external lemmas)." << std::endl);
      return false;
    }

    add_new_observed_var ();

    if (must_add_clause) {
      must_add_clause = false;
      add_lemma_idx = must_add_idx;

      forgettable = external_lemmas[must_add_idx]->forgettable;

      MLOGC ("true (forced clause addition, "
             << "forgettable: " << forgettable << " id: " << add_lemma_idx
             << ")." << std::endl);

      added_lemma_count++;
      return true;
    }

    if (added_lemma_count > lemma_per_cb) {
      added_lemma_count = 0;
      MLOGC ("false (lemma per CB treshold reached)." << std::endl);
      return false;
    }

    // Final model check will force to jump over some lemmas without
    // adding them. But if any of them is unsatisfied, it will force also
    // to set back the add_lemma_idx to them. So we do not need to start
    // the search here from 0.

    while (add_lemma_idx < external_lemmas.size ()) {

      if (!external_lemmas[add_lemma_idx]->add_count &&
          !external_lemmas[add_lemma_idx]->propagation_reason) {

        forgettable = external_lemmas[add_lemma_idx]->forgettable;

        MLOGC ("true (new lemma was found, "
               << "forgettable: " << forgettable << " id: " << add_lemma_idx
               << ")." << std::endl);

        added_lemma_count++;
        return true;
      }

      // Forgettable lemmas are added repeatedly to the solver only when
      // the final model falsifies it (recognized in cb_check_final_model).

      add_lemma_idx++;
    }
    MLOGC ("false." << std::endl);

    return false;
  }

  int cb_add_external_clause_lit () override {
    int lit = external_lemmas[add_lemma_idx]->next_lit ();

    MLOG ("cb_add_external_clause_lit "
          << lit << " (lemma " << add_lemma_idx << "/"
          << external_lemmas.size () << ")" << std::endl);

    if (!lit)
      external_lemmas[add_lemma_idx++]->add_count++;

    return lit;
  }

  int cb_decide () override {
    MLOG ("cb_decide starts." << std::endl);

    assert (compare_trails ());

    if (!unassigned_reasons.empty ()) {
#ifdef LOGGING
      MLOG ("clean up backtracked external propagation reasons: ");
      size_t del_count = 0;
#endif
      for (const auto &lit : unassigned_reasons) {
        size_t reason_id = reason_map[lit];
        assert (reason_id < external_lemmas.size ());
        external_lemmas[reason_id]->propagation_reason = false;
        external_lemmas[reason_id]->forgettable = true;
        reason_map.erase (lit);
#ifdef LOGGING
        MLOGC (lit << " ");
        del_count++;
#endif
      }
      MLOGC ("(" << del_count << " clauses)" << std::endl);
      unassigned_reasons.clear ();
    }

    if (observed_variables.empty () || observed_variables.size () <= 4) {
      MLOG ("cb_decide returns 0" << std::endl);
      return 0;
    }

    if (!(observed_variables.size () % 5) &&
        new_observed_variables.size ()) {
      int new_var = add_new_observed_var ();
      if (new_var) {
        MLOG ("cb_decide returns " << -1 * new_var << std::endl);
        return -1 * new_var;
      }
    }

    decision_loc++;

    if ((decision_loc % observed_variables.size ()) == 0) {
      if (!(observed_variables.size () % 11)) {
        MLOG ("cb_decide forces backtracking to level 1" << std::endl);
        s->force_backtrack (observed_variables.size () % 5);
      }
      size_t n = decision_loc / observed_variables.size ();
      if (n < observed_variables.size ()) {
        int lit = *std::next (observed_variables.begin (), n);
        MLOG ("cb_decide returns " << -1 * lit << std::endl);
        return -1 * lit;
      } else {
        MLOG ("cb_decide returns 0" << std::endl);
        return 0;
      }
    }
    MLOG ("cb_decide returns 0" << std::endl);
    return 0;
  }

  int cb_propagate () override {
    MLOGC ("cb_propagate starts" << std::endl);
    assert (compare_trails ());
    // if (observed_trail.size () < 2) {
    //   MLOG ("cb_propagate returns 0"
    //         << " (less than two observed variables are assigned)."
    //         << std::endl);

    //   return 0;
    // }

    size_t lit_sum = 0;  // sum of variables of satisfied observed literals
    int lowest_lit = 0;  // the lowest satisfied observed literal
    int highest_lit = 0; // the highest satisfied observed literal

    std::set<int> satisfied_literals =
        current_observed_satisfied_set (lit_sum, lowest_lit, highest_lit);

    if (satisfied_literals.empty ()) {
      MLOGC ("cb_propagate returns 0"
             << " (there are no observed satisfied literals)."
             << std::endl);
      return 0;
    }

    MLOGC (std::endl);
    assert (lowest_lit);
    assert (highest_lit);

    int unassigned_var = 0;
    for (auto v : observed_variables) {
      auto search = satisfied_literals.find (v);
      if (search == satisfied_literals.end ()) {
        search = satisfied_literals.find (-1 * v);
        if (search == satisfied_literals.end ()) {
          unassigned_var = v;
          break;
        }
      }
    }

    if (!unassigned_var) {
      MLOG ("cb_propagate returns 0"
            << " (there are no unassigned observed variables)."
            << std::endl);
      return 0;
    }

    assert (clause.empty ());
    int propagated_lit = 0;

    if (lit_sum % 5 == 0 && satisfied_literals.size () > 1) {
      clause = {unassigned_var, -1 * lowest_lit, -1 * highest_lit};
    } else if (lit_sum % 7 == 0 && satisfied_literals.size () > 0) {
      clause = {unassigned_var, -1 * highest_lit};
    } else if (lit_sum % 11 == 0) {
      clause = {unassigned_var};
    } else if (lit_sum > 15 && lowest_lit) {
      // Propagate a falsified literal, ok if lowest == highest
      clause = {-1 * lowest_lit, -1 * highest_lit};
    }

    if (!clause.empty ()) {
      propagated_lit = clause[0];
      size_t id = add_new_lemma (true);
      external_lemmas[id]->propagation_reason = true;
      reason_map[propagated_lit] = id;
      MLOG ("new clause added to reason map for "
            << propagated_lit << " with id " << id << std::endl);
      clause.clear ();
    }

    MLOG ("cb_propagate returns " << propagated_lit << std::endl);

    return propagated_lit;
  }

  std::set<int> current_observed_satisfied_set (size_t &lit_sum,
                                                int &lowest_lit,
                                                int &highest_lit) {

    lit_sum = 0;
    lowest_lit = 0;
    highest_lit = 0;
    std::set<int> satisfied_literals;

    for (auto level_lits : observed_trail) {
      for (auto lit : level_lits) {
        if (!s->observed (lit))
          continue;

        satisfied_literals.insert (lit);
        lit_sum += abs (lit);

        if (!lowest_lit)
          lowest_lit = lit;
        highest_lit = lit;
      }
    }

    return satisfied_literals;
  }

  int cb_add_reason_clause_lit (int plit) override {

    // At that point there is no need to assume that the trails are in
    // synchron.
    assert (reason_map.find (plit) != reason_map.end ());

    size_t reason_id = reason_map[plit];

    int lit = external_lemmas[reason_id]->next_lit ();

    if (!lit) {
      external_lemmas[reason_id]->add_count++;
      MLOG ("reason clause (id: " << reason_id << ") is added."
                                  << std::endl);
    }

    return lit;
  }

  void notify_assignment (const std::vector<int> &lits) override {
    MLOG ("notified " << lits.size () << " new assignments on level "
                      << observed_trail.size () - 1);
#ifndef NDEBUG
    MLOGC (": [ ");
#else
    MLOGC (std::endl);
#endif
    for (const auto &lit : lits) {
      observed_trail.back ().push_back (lit);
      unassigned_reasons.erase (lit);
#ifndef NDEBUG
      MLOGC (lit << " ");
#endif
    }
#ifndef NDEBUG
    MLOGC ("]" << std::endl);
#endif
  }

  void notify_new_decision_level () override {
    MLOG ("notify new decision level " << observed_trail.size () - 1
                                       << " -> " << observed_trail.size ()
                                       << std::endl);
    observed_trail.push_back (std::vector<int> ());
  }

  void notify_backtrack (size_t new_level) override {
    MLOG ("notify backtrack: " << observed_trail.size () - 1 << " -> "
                               << new_level << std::endl);
    assert (observed_trail.size () > 1 || !new_level);
    assert (observed_trail.size () == 1 ||
            observed_trail.size () >= new_level + 1);
    while (observed_trail.size () > new_level + 1) {
      // We can not remove reason clauses of backtracked assignments because
      // ILB might re-introduces them to the trail. Here we only save the
      // potential candidates to delete, and upon next cb_decide we delete
      // those ones that did not get re-assigned.
      for (auto lit : observed_trail.back ()) {
        if (reason_map.find (lit) != reason_map.end ()) {
          unassigned_reasons.insert (lit);
        }
      }
#ifndef NDEBUG
      MLOG ("unassign during backtrack from level "
            << observed_trail.size () - 1 << ": ");
      for (auto lit : observed_trail.back ()) {
        (void) lit;
        MLOGC (lit << " ");
      }
      MLOGC (std::endl);
#endif
      observed_trail.pop_back ();
    }
  }

  /* ----------------- ExternalPropagator functions end ------------------*/
};

// This is the class for the Mobical application.

class Mobical : public Handler {

  /*----------------------------------------------------------------------*/

  friend struct InitCall;
  friend struct FailedCall;
  friend struct ConcludeCall;
  friend class Reader;
  friend class Trace;
  friend struct ValCall;
  friend struct FlipCall;
  friend struct FlippableCall;
  friend struct MeltCall;
  friend class MockPropagator;
  friend struct ConnectCall;
  friend struct DisconnectCall;

  /*----------------------------------------------------------------------*/

  // We have the following modes, where 'RANDOM' mode can not be combined
  // with any other mode and 'OUTPUT' mode requires that 'SEED' or 'INPUT'
  // mode is set too, but it is not possible to combine 'SEED' and 'INPUT'.

  enum { RANDOM = 1, SEED = 2, INPUT = 4, OUTPUT = 8 };

  int mode = 0; // No 'Mode mode' due to 'mode |= ...' below.

  void check_mode_valid ();

  /*----------------------------------------------------------------------*/

  // Global options (set by parsing command line options in 'main').

  DoNot donot;
  Force force;
  bool verbose = false;
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
  bool bad_alloc = false;
  bool leak_alloc = false;
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

  void prefix () { cerr << prefix_string () << flush; }

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

  void print_statistics ();

  /*----------------------------------------------------------------------*/

  void die (const char *fmt, ...);
  void warning (const char *fmt, ...);

protected:
  /*----------------------------------------------------------------------*/

  MockPropagator
      *mock_pointer; // to be able to clean up withouth disconnect

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
//       (LEMMA|CONTINUE)*
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
// produce all these possible call sequences.  For instance it first adds
// all clauses before making assumptions and also does not mix in these
// 'ALWAYS' calls in all possible ways.

constexpr uint64_t shift (uint64_t bit) { return (uint64_t) 1 << bit; }

struct Call {

  enum Type : uint64_t {

    // clang-format off

    INIT            = shift (  0 ),
    SET             = shift (  1 ),
    CONFIGURE       = shift (  2 ),

    VARS            = shift (  3 ),
    ACTIVE          = shift (  4 ),
    REDUNDANT       = shift (  5 ),
    IRREDUNDANT     = shift (  6 ),
    RESERVE         = shift (  7 ),
                              
    PHASE           = shift (  8 ),
                              
    ADD             = shift (  9 ),
    ASSUME          = shift ( 10 ),

    SOLVE           = shift ( 11 ),
    SIMPLIFY        = shift ( 12 ),
    LOOKAHEAD       = shift ( 13 ),
    CUBING          = shift ( 14 ),
    PROPAGATE       = shift ( 15 ),

    VAL             = shift ( 16 ),
    FLIP            = shift ( 17 ),
    FLIPPABLE       = shift ( 18 ),
    FAILED          = shift ( 19 ),
    FIXED           = shift ( 20 ),

    FREEZE          = shift ( 21 ),
    FROZEN          = shift ( 22 ),
    MELT            = shift ( 23 ),

    LIMIT           = shift ( 24 ),
    OPTIMIZE        = shift ( 25 ),

    DUMP            = shift ( 26 ),
    STATS           = shift ( 27 ),

    RESET           = shift ( 28 ),

    CONSTRAIN       = shift ( 29 ),

    CONNECT         = shift ( 30 ),
    OBSERVE         = shift ( 31 ),
    LEMMA           = shift ( 32 ),

    CONCLUDE        = shift ( 33 ),
    DISCONNECT      = shift ( 34 ),

    TRACEPROOF      = shift ( 35 ),
    FLUSHPROOFTRACE = shift ( 36 ),
    CLOSEPROOFTRACE = shift ( 37 ),

#ifdef MOBICAL_MEMORY
    MAXALLOC        = shift ( 38 ),
    LEAKALLOC       = shift ( 39 ),
#endif

    // clang-format on

    ALWAYS = VARS | ACTIVE | REDUNDANT | IRREDUNDANT | FREEZE | FROZEN |
             MELT | LIMIT | OPTIMIZE | DUMP | STATS | RESERVE | FIXED |
             PHASE
#ifdef MOBICAL_MEMORY
             | MAXALLOC | LEAKALLOC
#endif
    ,
    CONFIG = INIT | SET | CONFIGURE | ALWAYS | TRACEPROOF,
    BEFORE =
        ADD | CONSTRAIN | ASSUME | ALWAYS | DISCONNECT | CONNECT | OBSERVE,
    PROCESS = SOLVE | SIMPLIFY | LOOKAHEAD | CUBING | PROPAGATE,
    DURING = LEMMA, // | CONTINUE,
    AFTER = VAL | FLIP | FLIPPABLE | FAILED | CONCLUDE | ALWAYS |
            FLUSHPROOFTRACE | CLOSEPROOFTRACE,
  };

  Type type; // Explicit typing.

  int arg;     // Argument if necessary.
  int64_t res; // Compute result if any.
  char *name;  // Option name for 'set' and 'config'
  int val;     // Option value for 'set'.

  Call (Type t, int a = 0, int r = 0, const char *o = 0, int v = 0)
      : type (t), arg (a), res (r), name (o ? strdup (o) : 0), val (v) {}

  virtual ~Call () {
    if (name)
      free (name);
  }

  virtual void execute (Solver *&) = 0;
  virtual void print (ostream &o) = 0;
  virtual const char *keyword () = 0;
  virtual Call *copy () = 0;
};

/*------------------------------------------------------------------------*/

static bool config_type (Call::Type t) {
  return (((int) t & (int) Call::CONFIG)) != 0;
}

static bool before_type (Call::Type t) {
  return (((int) t & (int) Call::BEFORE)) != 0;
}

static bool process_type (Call::Type t) {
  return (((int) t & (int) Call::PROCESS)) != 0;
}

static bool during_type (Call::Type t) {
  return (((int) t & (int) Call::DURING)) != 0;
}

static bool after_type (Call::Type t) {
  return (((int) t & (int) Call::AFTER)) != 0;
}

/*------------------------------------------------------------------------*/

// The model of valid API sequences is rather implicit.  First it is encoded
// in the random generator, by for instance adding options with 'set' only
// right after initialization through 'init', which is also enforced during
// parsing traces, but also in guards for executing certain API calls,
// marked 'CONTRACT' below.  For instance 'val' is only allowed if the
// solver is in the 'SATISFIED' state.

struct InitCall : public Call {
  InitCall () : Call (INIT) {}
  void execute (Solver *&s) { s = new Solver (); }
  void print (ostream &o) { o << "init" << endl; }
  Call *copy () { return new InitCall (); }
  const char *keyword () { return "init"; }
};

#ifdef MOBICAL_MEMORY
struct MaxAllocCall : public Call {
  MaxAllocCall (int val) : Call (MAXALLOC, 0, 0, 0, val) {}
  void execute (Solver *&s) { (void) s; }
  void print (ostream &o) { o << "max_alloc " << val << endl; }
  Call *copy () { return new MaxAllocCall (val); }
  const char *keyword () { return "max_alloc"; }
};
struct LeakAllocCall : public Call {
  LeakAllocCall () : Call (LEAKALLOC) {}
  void execute (Solver *&s) { (void) s; }
  void print (ostream &o) { o << "leak_alloc" << endl; }
  Call *copy () { return new LeakAllocCall (); }
  const char *keyword () { return "leak_alloc"; }
};
#endif

struct VarsCall : public Call {
  VarsCall () : Call (VARS) {}
  void execute (Solver *&s) { res = s->vars (); }
  void print (ostream &o) { o << "vars" << endl; }
  Call *copy () { return new VarsCall (); }
  const char *keyword () { return "vars"; }
};

struct ActiveCall : public Call {
  ActiveCall () : Call (ACTIVE) {}
  void execute (Solver *&s) { res = s->active (); }
  void print (ostream &o) { o << "active" << endl; }
  Call *copy () { return new ActiveCall (); }
  const char *keyword () { return "active"; }
};

struct RedundantCall : public Call {
  RedundantCall () : Call (REDUNDANT) {}
  void execute (Solver *&s) { res = s->redundant (); }
  void print (ostream &o) { o << "redundant" << endl; }
  Call *copy () { return new RedundantCall (); }
  const char *keyword () { return "redundant"; }
};

struct IrredundantCall : public Call {
  IrredundantCall () : Call (IRREDUNDANT) {}
  void execute (Solver *&s) { res = s->irredundant (); }
  void print (ostream &o) { o << "irredundant" << endl; }
  Call *copy () { return new IrredundantCall (); }
  const char *keyword () { return "irredundant"; }
};

struct ReserveCall : public Call {
  ReserveCall (int max_var) : Call (RESERVE, max_var) {}
  void execute (Solver *&s) { s->reserve (arg); }
  void print (ostream &o) { o << "reserve " << arg << endl; }
  Call *copy () { return new ReserveCall (arg); }
  const char *keyword () { return "reserve"; }
};

struct PhaseCall : public Call {
  PhaseCall (int max_var) : Call (PHASE, max_var) {}
  void execute (Solver *&s) { s->phase (arg); }
  void print (ostream &o) { o << "phase " << arg << endl; }
  Call *copy () { return new PhaseCall (arg); }
  const char *keyword () { return "phase"; }
};

struct SetCall : public Call {
  SetCall (const char *o, int v) : Call (SET, 0, 0, o, v) {}
  void execute (Solver *&s) { s->set (name, val); }
  void print (ostream &o) { o << "set " << name << ' ' << val << endl; }
  Call *copy () { return new SetCall (name, val); }
  const char *keyword () { return "set"; }
};

struct ConfigureCall : public Call {
  ConfigureCall (const char *o) : Call (CONFIGURE, 0, 0, o) {}
  void execute (Solver *&s) { s->configure (name); }
  void print (ostream &o) { o << "configure " << name << endl; }
  Call *copy () { return new ConfigureCall (name); }
  const char *keyword () { return "configure"; }
};

struct LimitCall : public Call {
  LimitCall (const char *o, int v) : Call (LIMIT, 0, 0, o, v) {}
  void execute (Solver *&s) { s->limit (name, val); }
  void print (ostream &o) { o << "limit " << name << ' ' << val << endl; }
  Call *copy () { return new LimitCall (name, val); }
  const char *keyword () { return "limit"; }
};

struct OptimizeCall : public Call {
  OptimizeCall (int v) : Call (OPTIMIZE, 0, 0, 0, v) {}
  void execute (Solver *&s) { s->optimize (val); }
  void print (ostream &o) { o << "optimize " << val << endl; }
  Call *copy () { return new OptimizeCall (val); }
  const char *keyword () { return "optimize"; }
};

struct ResetCall : public Call {
  ResetCall () : Call (RESET) {}
  void execute (Solver *&s) {
    delete s;
    s = 0;
  }
  void print (ostream &o) { o << "reset" << endl; }
  Call *copy () { return new ResetCall (); }
  const char *keyword () { return "reset"; }
};

struct AddCall : public Call {
  AddCall (int l) : Call (ADD, l) {}
  void execute (Solver *&s) { s->add (arg); }
  void print (ostream &o) { o << "add " << arg << endl; }
  Call *copy () { return new AddCall (arg); }
  const char *keyword () { return "add"; }
};

struct ConstrainCall : public Call {
  ConstrainCall (int l) : Call (CONSTRAIN, l) {}
  void execute (Solver *&s) { s->constrain (arg); }
  void print (ostream &o) { o << "constrain " << arg << endl; }
  Call *copy () { return new ConstrainCall (arg); }
  const char *keyword () { return "constrain"; }
};

struct ConnectCall : public Call {
  ConnectCall () : Call (CONNECT) {}
  void execute (Solver *&s) {
    // clean up if there was already one mock propagator
    MockPropagator *prev_pointer = 0;
    if (mobical.mock_pointer)
      prev_pointer = mobical.mock_pointer;
#ifdef LOGGING
    mobical.mock_pointer =
        new MockPropagator (s, mobical.add_set_log_to_true);
#else
    mobical.mock_pointer = new MockPropagator (s);
#endif
    s->connect_external_propagator (mobical.mock_pointer);
    s->connect_fixed_listener (mobical.mock_pointer);

    if (prev_pointer) {
      mobical.mock_pointer->add_prev_fixed (prev_pointer->observed_fixed);
      delete prev_pointer;
    } else {
      // FixedAssignmentListener does not replay previous fixed assignment,
      // collect them here explicitly -- EXPENSIVE
      // In practice FixedAssignmentListener is there from the beginning if
      // needed, in mobical we do not want to wire in this.

      mobical.mock_pointer->collect_prev_fixed ();
    }
  }
  void print (ostream &o) { o << "connect mock-propagator" << endl; }
  Call *copy () { return new ConnectCall (); }
  const char *keyword () { return "connect"; }
};

struct ObserveCall : public Call {
  ObserveCall (int l) : Call (OBSERVE, l) {}
  void execute (Solver *&s) {
    MockPropagator *mp =
        static_cast<MockPropagator *> (s->get_propagator ());
    if (mp) {
      mp->add_observed_lit (arg);
    }
  }
  void print (ostream &o) { o << "observe " << arg << endl; }
  Call *copy () { return new ObserveCall (arg); }
  const char *keyword () { return "observe"; }
};

struct LemmaCall : public Call {
  LemmaCall (int l) : Call (LEMMA, l) {}
  void execute (Solver *&s) {
    MockPropagator *mp =
        static_cast<MockPropagator *> (s->get_propagator ());

    if (mp && (!arg || s->observed (arg))) { // || mobical.donot.enforce
      mp->push_lemma_lit (arg);
    }
  }
  void print (ostream &o) { o << "lemma " << arg << endl; }
  Call *copy () { return new LemmaCall (arg); }
  const char *keyword () { return "lemma"; }
};

struct DisconnectCall : public Call {
  DisconnectCall () : Call (DISCONNECT) {}
  void execute (Solver *&s) {
    MockPropagator *mp =
        static_cast<MockPropagator *> (s->get_propagator ());
    if (mp)
      mp->remove_new_observed_var ();
    s->disconnect_fixed_listener ();
    s->disconnect_external_propagator ();
    if (mp) {
      delete mp;
      mobical.mock_pointer = 0;
    }
  }
  void print (ostream &o) { o << "disconnect mock-propagator" << endl; }
  Call *copy () { return new DisconnectCall (); }
  const char *keyword () { return "disconnect"; }
};

struct AssumeCall : public Call {
  AssumeCall (int l) : Call (ASSUME, l) {}
  void execute (Solver *&s) { s->assume (arg); }
  void print (ostream &o) { o << "assume " << arg << endl; }
  Call *copy () { return new AssumeCall (arg); }
  const char *keyword () { return "assume"; }
};

struct SolveCall : public Call {
  SolveCall (int r = 0) : Call (SOLVE, 0, r) {}
  void execute (Solver *&s) { res = s->solve (); }
  void print (ostream &o) { o << "solve " << res << endl; }
  Call *copy () { return new SolveCall (res); }
  const char *keyword () { return "solve"; }
};

struct SimplifyCall : public Call {
  SimplifyCall (int rounds, int r = 0) : Call (SIMPLIFY, rounds, r) {}
  void execute (Solver *&s) { res = s->simplify (arg); }
  void print (ostream &o) { o << "simplify " << arg << " " << res << endl; }
  Call *copy () { return new SimplifyCall (arg, res); }
  const char *keyword () { return "simplify"; }
};

struct LookaheadCall : public Call {
  LookaheadCall (int r = 0) : Call (LOOKAHEAD, 0, r) {}
  void execute (Solver *&s) { res = s->lookahead (); }
  void print (ostream &o) { o << "lookahead " << res << endl; }
  Call *copy () { return new LookaheadCall (res); }
  const char *keyword () { return "lookahead"; }
};

struct CubingCall : public Call {
  CubingCall (int r = 1) : Call (CUBING, 0, r) {}
  void execute (Solver *&s) { (void) s->generate_cubes (arg); }
  void print (ostream &o) { o << "cubing " << res << endl; }
  Call *copy () { return new CubingCall (res); }
  const char *keyword () { return "cubing"; }
};

struct PropagateCall : public Call {
  PropagateCall (int r = 0) : Call (PROPAGATE, 0, r) {}
  void execute (Solver *&s) {
    int res = s->propagate ();
    if (!res) {
      std::vector<int> implicants;
      s->get_entrailed_literals (implicants);
    }
  }
  void print (ostream &o) { o << "propagate " << res << endl; }
  Call *copy () { return new PropagateCall (res); }
  const char *keyword () { return "propagate"; }
};

struct ValCall : public Call {
  ValCall (int l, int r = 0) : Call (VAL, l, r) {}
  void execute (Solver *&s) {
    if (mobical.donot.enforce)
      res = s->val (arg);
    else if (s->state () == SATISFIED)
      res = s->val (arg);
    else
      res = 0;
  }
  void print (ostream &o) { o << "val " << arg << ' ' << res << endl; }
  Call *copy () { return new ValCall (arg, res); }
  const char *keyword () { return "val"; }
};

struct FlipCall : public Call {
  FlipCall (int l, int r = 0) : Call (FLIP, l, r) {}
  void execute (Solver *&s) {
    if (mobical.donot.enforce)
      res = s->flip (arg);
    else if (s->state () == SATISFIED)
      res = s->flip (arg);
    else
      res = 0;
  }
  void print (ostream &o) { o << "flip " << arg << ' ' << res << endl; }
  Call *copy () { return new FlipCall (arg, res); }
  const char *keyword () { return "flip"; }
};

struct FlippableCall : public Call {
  FlippableCall (int l, int r = 0) : Call (FLIPPABLE, l, r) {}
  void execute (Solver *&s) {
    if (mobical.donot.enforce)
      res = s->flippable (arg);
    else if (s->state () == SATISFIED)
      res = s->flippable (arg);
    else
      res = 0;
  }
  void print (ostream &o) {
    o << "flippable " << arg << ' ' << res << endl;
  }
  Call *copy () { return new FlipCall (arg, res); }
  const char *keyword () { return "flippable"; }
};

struct FixedCall : public Call {
  FixedCall (int l, int r = 0) : Call (FIXED, l, r) {}
  void execute (Solver *&s) { res = s->fixed (arg); }
  void print (ostream &o) { o << "fixed " << arg << ' ' << res << endl; }
  Call *copy () { return new FixedCall (arg, res); }
  const char *keyword () { return "fixed"; }
};

struct FailedCall : public Call {
  FailedCall (int l, int r = 0) : Call (FAILED, l, r) {}
  void execute (Solver *&s) {
    if (mobical.donot.enforce)
      res = s->failed (arg);
    else if (s->state () == UNSATISFIED)
      res = s->failed (arg);
    else
      res = 0;
  }
  void print (ostream &o) { o << "failed " << arg << ' ' << res << endl; }
  Call *copy () { return new FailedCall (arg, res); }
  const char *keyword () { return "failed"; }
};

struct ConcludeCall : public Call {
  ConcludeCall () : Call (CONCLUDE) {}
  void execute (Solver *&s) {
    if (mobical.donot.enforce)
      s->conclude ();
    else if (s->state () == UNSATISFIED || s->state () == SATISFIED)
      s->conclude ();
    res = 0;
  }
  void print (ostream &o) { o << "conclude" << endl; }
  Call *copy () { return new ConcludeCall (); }
  const char *keyword () { return "conclude"; }
};

struct FreezeCall : public Call {
  FreezeCall (int l) : Call (FREEZE, l) {}
  void execute (Solver *&s) { s->freeze (arg); }
  void print (ostream &o) { o << "freeze " << arg << endl; }
  Call *copy () { return new FreezeCall (arg); }
  const char *keyword () { return "freeze"; }
};

struct MeltCall : public Call {
  MeltCall (int l) : Call (MELT, l) {}
  void execute (Solver *&s) {
    if (mobical.donot.enforce || s->frozen (arg))
      s->melt (arg);
  }
  void print (ostream &o) { o << "melt " << arg << endl; }
  Call *copy () { return new MeltCall (arg); }
  const char *keyword () { return "melt"; }
};

struct FrozenCall : public Call {
  FrozenCall (int l, int r = 0) : Call (FROZEN, l, r) {}
  void execute (Solver *&s) { res = s->frozen (arg); }
  void print (ostream &o) { o << "frozen " << arg << ' ' << res << endl; }
  Call *copy () { return new FrozenCall (arg, res); }
  const char *keyword () { return "frozen"; }
};

struct DumpCall : public Call {
  DumpCall () : Call (DUMP) {}
  void execute (Solver *&s) { s->dump_cnf (); }
  void print (ostream &o) { o << "dump" << endl; }
  Call *copy () { return new DumpCall (); }
  const char *keyword () { return "dump"; }
};

struct StatsCall : public Call {
  StatsCall () : Call (STATS) {}
  void execute (Solver *&s) { s->statistics (); }
  void print (ostream &o) { o << "stats" << endl; }
  Call *copy () { return new StatsCall (); }
  const char *keyword () { return "stats"; }
};

struct TraceProofCall : public Call {
  std::string path;
  TraceProofCall (const string &p) : Call (TRACEPROOF), path (p) {}
  void execute (Solver *&s) { s->trace_proof (path.c_str ()); }
  void print (ostream &o) { o << "trace_proof" << ' ' << path << endl; }
  Call *copy () { return new TraceProofCall (path); }
  const char *keyword () { return "trace_proof"; }
};

struct FlushProofTraceCall : public Call {
  FlushProofTraceCall () : Call (FLUSHPROOFTRACE) {}
  void execute (Solver *&s) { s->flush_proof_trace (); }
  void print (ostream &o) { o << "flush_proof_trace" << endl; }
  Call *copy () { return new FlushProofTraceCall (); }
  const char *keyword () { return "flush_proof_trace"; }
};

struct CloseProofTraceCall : public Call {
  CloseProofTraceCall () : Call (CLOSEPROOFTRACE) {}
  void execute (Solver *&s) { s->close_proof_trace (); }
  void print (ostream &o) { o << "close_proof_trace" << endl; }
  Call *copy () { return new CloseProofTraceCall (); }
  const char *keyword () { return "close_proof_trace"; }
};

/*------------------------------------------------------------------------*/

class Trace {

  int64_t id;
  uint64_t seed;

  Solver *solver;
  vector<Call *> calls;

  friend class Reader;

public:
  static int64_t generated;
  static int64_t executed;
  static int64_t failed;
  static int64_t ok;

#ifdef MOBICAL_MEMORY
  static int64_t memory_call_index;
  static int64_t memory_bad_alloc;
  static int64_t memory_bad_size;
  static int64_t memory_bad_failed;
  static int64_t memory_leak_alloc;
  static int64_t memory_leak_next_free;
#endif

#define SIGNALS \
  SIGNAL (SIGINT) \
  SIGNAL (SIGSEGV) \
  SIGNAL (SIGABRT) \
  SIGNAL (SIGTERM) \
  SIGNAL (SIGBUS) \
  SIGNAL (SIGUSR1) \
  SIGNAL (SIGUSR2)

#define SIGNAL(SIG) static void (*old_##SIG##_handler) (int);
  SIGNALS
#undef SIGNAL
  static void child_signal_handler (int);
  static void init_child_signal_handlers ();
  static void reset_child_signal_handlers ();

#ifdef MOBICAL_MEMORY
  static void hooks_install (void);
  static void hooks_uninstall (void);
  static void *hook_malloc (size_t);
  static void *hook_realloc (void *, size_t);
  static void hook_free (void *);
  static void print_trace (void **, size_t, ostream &, size_t);
#endif

  Trace (int64_t i = 0, uint64_t s = 0) : id (i), seed (s), solver (0) {}

  void clear () {
    while (!calls.empty ()) {
      Call *c = calls.back ();
      delete c;
      calls.pop_back ();
    }
    if (solver)
      delete solver;
    solver = 0;
  }

  ~Trace () { clear (); }

  void push_back (Call *c) { calls.push_back (c); }

  void print (ostream &o) {
    for (size_t i = 0; i < calls.size (); i++) {
#ifdef MOBICAL_MEMORY
      if (mobical.shared->bad_alloc.alloc_call_index == i + 1)
        o << "# "
             "V------------------------------------------------------------"
             "---------- bad alloc: allocation"
          << endl;
      if (mobical.shared->bad_alloc.signal_call_index == i + 1)
        o << "# "
             "V------------------------------------------------------------"
             "---------- bad alloc: crashed"
          << endl;
      if (mobical.shared->bad_alloc.debug_filter_index == i + 1)
        o << "# "
             "V------------------------------------------------------------"
             "---------- debug: call was filtered"
          << endl;
      for (size_t index{0u}; index < MOBICAL_MEMORY_LEAK_COUNT; index++) {
        if (mobical.shared->leak_alloc.call_index[index] == i + 1) {
          o << "# "
               "V----------------------------------------------------------"
               "------------ leak alloc: allocation"
            << endl;
          break;
        }
      }
#endif
      o << i << ' ';
      calls[i]->print (o);
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
      o << "# A crash happened here:" << endl;
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

    executed++;
    bool first = true;
    bool deallocated = false;
    for (size_t i = 0; i < calls.size (); i++) {
      Call *c = calls[i];

#ifdef MOBICAL_MEMORY
      memory_call_index = i + 1;
      if (memory_bad_failed && c->type != Call::RESET) {
        continue; // Ignore call, only RESET (deallocation) allowed.
      }
#else
      (void) deallocated;
#endif

      try {
        // They are (ideally) are executed already
        if (c->type == Call::LEMMA)
          continue;
        // if (c->type == Call::CONTINUE)
        //   continue;
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
          deallocated = true;
        }
#endif

        if (c->type == Call::SOLVE) {
          // Look ahead and collect LemmaCalls to be executed
          // before solve is executed
          for (size_t j = i + 1; j < calls.size (); j++) {
            Call *next_c = calls[j];
            if (next_c->type == Call::LEMMA)
              next_c->execute (solver);
            else
              break;
          }
        }
        if (mobical.shared && process_type (c->type)) {
          mobical.shared->solved++;
          if (first)
            first = false;
          else
            mobical.shared->incremental++;
          c->execute (solver);
          if (c->res == 10)
            mobical.shared->sat++;
          if (c->res == 20)
            mobical.shared->unsat++;
        } else
          c->execute (solver);
      } catch (const std::bad_alloc &e) {
        // Ignore out-of-memory errors and assume solver state is
        // consistent.
        mobical.shared->oom++;
      }
    }
#ifdef MOBICAL_MEMORY
    if (deallocated && mobical.mock_pointer) {
      delete mobical.mock_pointer;
      mobical.mock_pointer = nullptr;
    }
    hooks_uninstall ();
    // Note: Do not force-deallocate here as otherwise the shrink procedure
    // will remove the RESET call.
    if (deallocated) {
      for (size_t index{0u}; index < MOBICAL_MEMORY_LEAK_COUNT; index++) {
        if (mobical.shared->leak_alloc.alloc_ptr[index] != nullptr) {
          reset_child_signal_handlers ();
          raise (SIGUSR2);
        }
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
      if (process_type (c->type))
        last = true;
    }
    return res;
  }

  size_t size () { return calls.size (); }
  Call *operator[] (size_t i) { return calls[i]; }

  void generate (uint64_t id, uint64_t seed);

  int fork_and_execute ();
  void shrink (int expected);

  void write_prefixed_seed (const char *prefix);
  void write_path (const char *path);

  static bool ignored_option (const char *name);
  bool ignore_option (const char *, int max_var);
  int64_t option_high_value (const char *, int64_t def, int64_t lo,
                             int64_t hi);

private:
  void notify (char ch = 0) { mobical.notify (*this, ch); }
  void progress () { mobical.progress (*this); }

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
  bool shrink_clauses (int expected);
  bool shrink_userphases (int expected);
  bool shrink_lemmas (int expected);
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
  void generate_reserve (Random &, int vars);
  void generate_clause (Random &, int minvars, int maxvars, int uniform);
  void generate_constraint (Random &, int minvars, int maxvars,
                            int uniform);
  void generate_assume (Random &, int vars);
  void generate_process (Random &);
  void generate_values (Random &, int vars);
  void generate_flipped (Random &, int vars);
  void generate_frozen (Random &, int vars);
  void generate_failed (Random &, int vars);
  void generate_conclude (Random &);
  void generate_freeze (Random &, int vars);
  void generate_melt (Random &);

  void generate_propagator (Random &, int minvars, int maxvars);
  void generate_lemmas (Random &);

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

  int next () { return getc (file); }

  void error (const char *fmt, ...);

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
// option 'name'.  Here we assume that an option disables another one if the
// disabling one has as name proper prefix of the disabled one and the value
// of the former is set to zero in the trace.
//
bool Trace::ignore_option (const char *name, int max_var) {

  if (ignored_option (name))
    return true;

  // There are options which should be kept at their default value unless
  // the formula is really small.  Otherwise the solver might run 'forever'.
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
// the option value above the default and similarly for elimination bounds.
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

    // We ignore logging here and set it below to make mobical deterministic
    if (!strcmp (o.name, "log"))
      continue;
    if (!strcmp (o.name, "logsort"))
      continue;
    // We keep choosing the value for 'simplify' and 'walk' out of the loop
    // (see the arguments described above).
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

  // Now setting the option for logging. Even if we do not generate the log
  // call, we need the side effect of generate_bool ()
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
#ifdef LOGGING
  if (mobical.add_set_log_to_true)
    push_back (new SetCall ("log", 1));
#else
  if (mobical.add_set_log_to_true)
    mobical.warning ("ignoring log option");
#endif
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

void Trace::generate_reserve (Random &random, int max_var) {
  if (random.generate_double () > 0.01)
    return;
  int new_max_var = random.pick_int (0, 1.1 * max_var);
  push_back (new ReserveCall (new_max_var));
}

/*------------------------------------------------------------------------*/

void Trace::generate_limits (Random &random) {
  if (random.generate_double () < 0.05)
    push_back (new LimitCall ("terminate", random.pick_log (0, 1e5)));
  if (random.generate_double () < 0.05)
    push_back (new LimitCall ("conflicts", random.pick_log (0, 1e4)));
  if (random.generate_double () < 0.05)
    push_back (new LimitCall ("decisions", random.pick_log (0, 1e4)));
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
}

/*------------------------------------------------------------------------*/

void Trace::generate_propagator (Random &random, int minvars, int maxvars) {
  if (random.generate_double () < 0.9)
    return;

  assert (minvars <= maxvars);
  if (in_connection)
    push_back (new DisconnectCall ());
  push_back (new ConnectCall ());

  in_connection = true;

  observed_vars.clear ();

  // Give a chance to add no observed variables at all
  if (random.generate_double () < 0.05)
    return;

  for (int idx = minvars; idx <= maxvars; idx++) {
    if (random.generate_double () < 0.6)
      continue;
    int lit = random.generate_bool () ? -idx : idx;
    push_back (new ObserveCall (lit));
    observed_vars.push_back (abs (lit));
  }
  push_back (new ObserveCall (0));
  for (int idx = maxvars + 1; idx <= maxvars * 1.5; idx++) {
    if (random.generate_double () < 0.75)
      continue;
    int lit = random.generate_bool () ? -idx : idx;
    push_back (new ObserveCall (lit));
    observed_vars.push_back (abs (lit));
  }
}

void Trace::generate_lemmas (Random &random) {
  if (!observed_vars.size ())
    return;
  int nof_user_propagation_phases = random.pick_int (4, 7);

  for (int p = 0; p < nof_user_propagation_phases; p++) {
    if (random.generate_double () < 0.05) {
      // push_back (new ContinueCall ());
    } else {
      const int nof_lemmas = random.pick_int (5, 11);
      const int ovars = observed_vars.size ();
      for (int i = 0; i < nof_lemmas; i++) {
        // Tiny tiny chance to generate an empty lemma
        if (random.generate_double () < 0.005) {
          push_back (new LemmaCall (0));
        } else {
          int count = pick_size (random, 4);
          if (count > ovars)
            count = ovars;
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
            push_back (new LemmaCall (lit));
          }

          delete[] picked;
          if (random.generate_double () < 0.1) {
            int idx = random.pick_int (0, max_idx);
            int lit = random.generate_bool () ? -observed_vars[idx]
                                              : observed_vars[idx];
            push_back (new LemmaCall (lit));
          }
          push_back (new LemmaCall (0));
        }
      }
      // push_back (new ContinueCall ());
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
    push_back (new ValCall (lit));
  }
  if (random.generate_double () < 0.1) {
    int idx = random.pick_int (vars + 1, vars * 1.5 + 1);
    int lit = random.generate_bool () ? -idx : idx;
    push_back (new ValCall (lit));
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
  if (random.generate_double () < 0.05)
    return;
  if (random.generate_double () < 0.05) {
    push_back (new ConcludeCall ());
  }
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
      assert (idx), assert (idx <= m);
      assert (frozen[idx] > 0);
      frozen[idx]--;
    } else if (c->type == Call::FREEZE) {
      int idx = abs (c->arg);
      assert (idx), assert (idx <= m);
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
    if (in_connection && observed_vars.size ())
      generate_lemmas (random);
  } else if (fraction > 0.99) {
    const int depth = random.pick_int (0, 10);
    push_back (new CubingCall (depth));
  } else if (fraction > 0.9) {
    push_back (new LookaheadCall ());
  } else if (fraction > 0.85) {
    push_back (new PropagateCall ());
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

#ifdef MOBICAL_MEMORY
  if (mobical.bad_alloc && (random.pick_int (0, 2) == 0)) {
    push_back (new MaxAllocCall (random.pick_log (1e2, 1e6)));
  }
  if (mobical.leak_alloc && (random.pick_int (0, 2) == 0)) {
    push_back (new LeakAllocCall ());
  }
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
      generate_queries (random), generate_reserve (random, maxvars),
          generate_clause (random, minvars, maxvars, uniform);

    if (in_connection && random.generate_bool ()) {
      observed_vars.clear ();
      push_back (new DisconnectCall ());
      in_connection = false;
    } else {
      generate_propagator (random, minvars, maxvars);
    }

    generate_constraint (random, minvars, maxvars, uniform);
    generate_assume (random, maxvars);
    generate_melt (random);
    generate_freeze (random, maxvars);
    generate_limits (random);

    generate_process (random);

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

void Mobical::print_statistics () {
  hline ();

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
      cerr << "out-of-time " << shared->timeout << ", " << "out-of-memory "
           << shared->memout << endl
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

#ifdef MOBICAL_MEMORY
int64_t Trace::memory_call_index = -1;
int64_t Trace::memory_bad_alloc = 0;
int64_t Trace::memory_bad_size = 0;
int64_t Trace::memory_bad_failed = 0;
int64_t Trace::memory_leak_alloc = 0;
int64_t Trace::memory_leak_next_free = 0;
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
    mobical.shared->bad_alloc.signal_call_index = memory_call_index;
    mobical.shared->bad_alloc.signal_stack_size =
        backtrace (mobical.shared->bad_alloc.signal_stack_array,
                   MOBICAL_MEMORY_STACK_COUNT);
    // The signal probably has been raised as a result
    // of the forced failed memory allocation.
    // Raise a custom signal code for the parent to
    // create a unique result code (2 instead of 1).
    reset_child_signal_handlers ();
    raise (SIGUSR1);
  }
#endif

  struct rusage u;
  if (!getrusage (RUSAGE_SELF, &u)) {
    if ((int64_t) u.ru_maxrss >> 10 >= mobical.space_limit) {
      if (mobical.shared)
        mobical.shared->memout++;
      // Since there is no memout signal we just misuse SIXCPU to notify the
      // calling process that this is a out-of-resource situation.
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
      mobical.shared->bad_alloc.alloc_call_index = memory_call_index;
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
      mobical.shared->leak_alloc.call_index[index] = memory_call_index;
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
      mobical.shared->bad_alloc.alloc_call_index = memory_call_index;
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
      mobical.shared->leak_alloc.call_index[index] = memory_call_index;
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
      mobical.shared->leak_alloc.call_index[index] = memory_call_index;
      mobical.shared->leak_alloc.stack_size[index] =
          backtrace (mobical.shared->leak_alloc.stack_array[index],
                     MOBICAL_MEMORY_STACK_COUNT);
      memory_leak_next_free = index + 1;
      hooks_install ();
      return new_ptr;
    }

    hooks_uninstall ();
    printf ("No free slot!");
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

void Trace::print_trace (void **stack_array, size_t stack_size, ostream &os,
                         size_t start_index) {
  char **stack_text = backtrace_symbols (stack_array, stack_size);
  for (size_t stack_index = start_index; stack_index < stack_size;
       stack_index++) {
    string stack_entry = stack_text[stack_index];
    if (size_t position = stack_entry.rfind ("/");
        position != string::npos) {
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

    int status, other = wait (&status);
    if (other != child)
      res = 0;
    else if (WIFEXITED (status))
      res = WEXITSTATUS (status);
    else if (!WIFSIGNALED (status))
      res = 0;
    else if (mobical.donot.ignore_resource_limits)
      res = 1;
    else if (WTERMSIG (status) == SIGUSR1)
      res = 2; // Bad allocation caused signal.
    else if (WTERMSIG (status) == SIGUSR2)
      res = 3; // Leaked allocation caused signal.
    else
      res = (WTERMSIG (status) != SIGXCPU);

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
    if (mobical.donot.fork)
      mobical.mock_pointer = nullptr;
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
  Trace shrunken;
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
          ignore[j] = true;
      }
      Trace tmp;
      tmp.clear ();
      for (size_t i = 0; i < size (); i++)
        if (!ignore[i])
          tmp.push_back (calls[i]->copy ());
      progress ();
      if (tmp.fork_and_execute () != expected) { // failed
        for (size_t i = l; i < r; i++)
          removed[i] = saved[i];
      } else {
        shrunken.clear ();
        for (size_t i = 0; i < tmp.size (); i++)
          shrunken.push_back (tmp[i]->copy ());
        res = true; // succeeded to shrink
      }
    }
    if (granularity == 1)
      break;
    granularity = (granularity + 1) / 2;
    if (shrunken.size ())
      shrunken.clear ();
  }
  if (res) {
    for (size_t i = 0; i < size (); i++)
      ignore[i] = false;
    for (size_t i = 0; i < n; i++) {
      if (!removed[i])
        continue;
      Segment &s = segments[i];
      for (size_t j = s.lo; j < s.hi; j++)
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
    cerr << left << setw (13) << "reduce:";
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
  for (l = 1; l < size () && config_type (calls[l]->type); l++)
    ;
  Segments segments;
  size_t r;
  for (; l < size (); l = r) {
    for (r = l; r < size () && before_type (calls[r]->type); r++)
      ;
    if (r < size () && process_type (calls[r]->type))
      r++;
    for (; r < size () && during_type (calls[r]->type); r++)
      ;
    for (; r < size () && after_type (calls[r]->type); r++)
      ;
    if (l < r)
      segments.push_back (Segment (l, r));
    else {
      assert (l == r);
      if (!config_type (calls[r]->type))
        segments.push_back (Segment (r, r + 1));
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
    while (l > 0 && (c->type != Call::ADD || c->arg))
      c = calls[--l];
    if (!l)
      break;
    r = l + 1;
    while ((c = calls[--l])->type == Call::ADD && c->arg)
      ;
    segments.push_back (Segment (++l, r));
  }
  return shrink_segments (segments, expected);
}

bool Trace::shrink_userphases (int expected) {
  // TODO: introduce donot-shrink-lemmas
  // if (mobical.donot.shrink.lemmas) return false;
  notify ('a');
  Segments segments;
  size_t r;
  size_t l = 1;
  for (; l < size () && !during_type (calls[l]->type); l++)
    ;
  for (; l < size (); l++) {
    if (!during_type (calls[l]->type))
      continue;
    r = l;
    while (r < size () && calls[r]->type == Call::LEMMA)
      r++;
    // assert (calls[r]->type == Call::CONTINUE);
    // if (r < size () && calls[r]->type == Call::CONTINUE) {
    //   segments.push_back (Segment (l, r + 1));
    //   l = r;
    // }
  }
  return shrink_segments (segments, expected);
}

bool Trace::shrink_lemmas (int expected) {
  // TODO: introduce donot-shrink-lemmas
  // if (mobical.donot.shrink.lemmas) return false;
  notify ('u');
  Segments segments;
  for (size_t r = size (), l; r > 1; r = l) {
    Call *c = calls[l = r - 1];
    while (l > 0 && (c->type != Call::LEMMA || c->arg))
      c = calls[--l];
    if (!l)
      break;
    r = l + 1;
    while ((c = calls[--l])->type == Call::LEMMA && c->arg)
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
    if (c->type == Call::ADD && c->arg)
      segments.push_back (Segment (l, l + 1));
    if (c->type == Call::LEMMA && c->arg)
      segments.push_back (Segment (l, l + 1));
  }
  return shrink_segments (segments, expected);
}

static bool is_basic (Call *c) {
  switch ((uint64_t) c->type) {
  case Call::ASSUME:
  case Call::SOLVE:
  case Call::SIMPLIFY:
  case Call::LOOKAHEAD:
  case Call::CUBING:
  case Call::PROPAGATE:
  case Call::VARS:
  case Call::ACTIVE:
  case Call::REDUNDANT:
  case Call::IRREDUNDANT:
  case Call::RESERVE:
  case Call::VAL:
  case Call::FLIP:
  case Call::FLIPPABLE:
  case Call::FIXED:
  case Call::FAILED:
  case Call::FROZEN:
  case Call::CONCLUDE:
  case Call::FREEZE:
  case Call::MELT:
  case Call::LIMIT:
  case Call::OPTIMIZE:
  case Call::OBSERVE:
    return true;
  default:
    return false;
  }
}

bool Trace::shrink_basic (int expected) {
  if (mobical.donot.shrink.basic)
    return false;
  notify ('b');
  Segments segments;
  for (size_t l = size () - 1; l > 0; l--) {
    Call *c = calls[l];
    if (!is_basic (c))
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
    if (!(c->type == Call::INIT || c->type == Call::MAXALLOC)) {
#else
    if (!(c->type == Call::INIT)) {
#endif
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
#ifdef MOBICAL_MEMORY
      } else if (c->type == Call::MAXALLOC) {
        lo = 0, hi = c->val;
#endif
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

      // Now we do a delta-debugging inspired binary search for the smallest
      // value for which the execution produces a non-zero exit code.  It
      // kind of assumes monotonicity and if this is not the case might not
      // yield the smallest value, but remains logarithmic.
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

static bool has_lit_arg_type (Call *c) {
  switch ((uint64_t) c->type) {
  case Call::ADD:
  case Call::CONSTRAIN:
  case Call::ASSUME:
  case Call::FREEZE:
  case Call::MELT:
  case Call::FROZEN:
  case Call::FLIP:
  case Call::FLIPPABLE:
  case Call::FIXED:
  case Call::FAILED:
  case Call::RESERVE:
  case Call::LEMMA:
  case Call::OBSERVE:
    return true;
  default:
    return false;
  }
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
      if (!has_lit_arg_type (c))
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
      if (!c->arg || c->arg == INT_MIN)
        mapped.push_back (c->copy ());
      else if (has_lit_arg_type (c)) {
        int new_lit = variables[abs (c->arg)];
        assert (0 < new_lit), assert (new_lit <= max_idx);
        if (c->arg < 0)
          new_lit = -new_lit;
        Call *d = c->copy ();
        d->arg = new_lit;
        mapped.push_back (d);
      } else
        mapped.push_back (c->copy ());
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
    LEMMAS,
    UPHASES, // How many times the propagator answers
    LITERALS,
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
    if (l != CLAUSES && shrink_clauses (expected))
      s = true, l = CLAUSES;
    if (l != UPHASES && shrink_userphases (expected))
      s = true, l = UPHASES;
    if (l != LEMMAS && shrink_lemmas (expected))
      s = true, l = LEMMAS;
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

void Trace::write_path (const char *path) {
  if (!strcmp (path, "-"))
    print (cout);
  else {
    ofstream os (path);
    if (!os.is_open ())
      mobical.die ("can not write '%s'", path);
    print (os);
  }
}

void Trace::write_prefixed_seed (const char *prefix) {
  ostringstream ss;
  ss << prefix << '-' << setfill ('0') << right << setw (20) << seed
     << ".trace" << flush;
  ofstream os (ss.str ().c_str ());
  if (!os.is_open ())
    mobical.die ("can not write '%s'", ss.str ().c_str ());
  print (os);
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
  int ch, lit = 0, val = 0, adding = 0, constraining = 0, lemma_adding = 0,
          solved = 0;
  uint64_t state = 0;
  const bool enforce = !mobical.donot.enforce;
  Call *before_trigger = 0;
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
    }
    assert (n < sizeof line);
    line[n] = 0;
    char *p = line;
    if (isdigit (ch = *p)) {
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
    const char *first = 0, *second = 0;
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
          *p = 0;
          error ("unexpected space after second argument '%s'", second);
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
    } else if (!strcmp (keyword, "reserve")) {
      if (!first)
        error ("argument to 'reserve' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'reserve'", first);
      if (second)
        error ("additional argument '%s' to 'reserve'", second);
      c = new ReserveCall (lit);
    } else if (!strcmp (keyword, "phase")) {
      if (!first)
        error ("argument to 'phase' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'phase'", first);
      if (second)
        error ("additional argument '%s' to 'phase'", second);
      c = new PhaseCall (lit);
    } else if (!strcmp (keyword, "add")) {
      if (!first)
        error ("argument to 'add' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'add'", first);
      if (second)
        error ("additional argument '%s' to 'add'", second);
      if (enforce && lit == INT_MIN)
        error ("invalid literal '%d' as argument to 'add'", lit);
      adding = lit;
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
      constraining = lit;
      c = new ConstrainCall (lit);
    } else if (!strcmp (keyword, "connect")) {
      c = new ConnectCall ();
    } else if (!strcmp (keyword, "disconnect")) {
      c = new DisconnectCall ();
    } else if (!strcmp (keyword, "observe")) {
      if (!first)
        error ("argument to 'observe' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'observe'", first);
      if (second)
        error ("additional argument '%s' to 'observe'", second);
      c = new ObserveCall (lit);
    } else if (!strcmp (keyword, "lemma")) {
      if (!first)
        error ("argument to 'lemma' missing");
      if (!parse_int_str (first, lit))
        error ("invalid argument '%s' to 'lemma'", first);
      if (second)
        error ("additional argument '%s' to 'lemma'", second);
      // if (!lemma_adding && !lit) error ("empty lemma is learned.");
      lemma_adding = lit;
      c = new LemmaCall (lit);
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
        c = new PropagateCall (lit);
      else
        c = new PropagateCall ();
    } else if (!strcmp (keyword, "val")) {
      if (!first)
        error ("first argument to 'val' missing");
      if (!parse_int_str (first, lit))
        error ("invalid first argument '%s' to 'val'", first);
      if (enforce && (!lit || lit == INT_MIN))
        error ("invalid literal '%d' as argument to 'val'", lit);
      if (second && !parse_int_str (second, val))
        error ("invalid second argument '%s' to 'val'", second);
      if (second && val != -1 && val != 0 && val != -1)
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
      if (second && val != -1 && val != 0 && val != -1)
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
        error ("option --bad-alloc has to be anabled for max_alloc calls");
      if (!first)
        error ("first argument to 'max_alloc' missing");
      if (!parse_int_str (first, val))
        error ("invalid first argument '%s' to 'max_alloc'", first);
      c = new MaxAllocCall (val);
    } else if (!strcmp (keyword, "leak_alloc")) {
      if (!mobical.leak_alloc)
        error (
            "option --leak-alloc has to be anabled for leak_alloc calls");
      c = new LeakAllocCall ();
#endif
    } else
      error ("invalid keyword '%s'", keyword);

    // This checks the legal structure of traces described above.
    //
    if (enforce) {
#ifdef MOBICAL_MEMORY
      if (!state && !(c->type & (Call::INIT | Call::MAXALLOC)))
#else
      if (!state && !(c->type == Call::INIT))
#endif
        error ("first call has to be an 'init' or 'maxalloc' call");

      if (state == Call::RESET)
        error ("'%s' after 'reset'", c->keyword ());

      if (adding && c->type != Call::ADD && c->type != Call::RESET)
        error ("'%s' after 'add %d' without 'add 0'", c->keyword (),
               adding);

      if (lemma_adding && c->type != Call::LEMMA && c->type != Call::RESET)
        error ("'%s' after 'lemma %d' without 'lemma 0'", c->keyword (),
               lemma_adding);

      if (constraining && c->type != Call::FIXED &&
          c->type != Call::CONSTRAIN && c->type != Call::RESET)
        error ("'%s' after 'constrain %d' without 'constrain 0'",
               c->keyword (), constraining);

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
      case Call::OBSERVE:
        if (state != Call::BEFORE)
          before_trigger = c;
        new_state = Call::BEFORE;
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
                state == Call::LEMMA || state == Call::AFTER);
        new_state = Call::AFTER;
        break;

      case Call::SOLVE:
      case Call::SIMPLIFY:
      case Call::LOOKAHEAD:
      case Call::CUBING:
      case Call::PROPAGATE:
      case Call::RESET:
      case Call::CONNECT:
      case Call::LEMMA:
      // case Call::CONTINUE:
      case Call::DISCONNECT:
        new_state = c->type;
        break;

      default:
        break;
      }

      state = new_state;
    }

#ifdef LOGGING
    if (trace.size () == 1 && mobical.add_set_log_to_true)
      trace.push_back (new SetCall ("log", 1));
#endif

    if (c && mobical.add_dump_before_solve && process_type (c->type))
      trace.push_back (new DumpCall ());

    trace.push_back (c);

    if (c && mobical.add_stats_after_solve && process_type (c->type))
      trace.push_back (new StatsCall ());

    lineno++;
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
#endif

Mobical::Mobical () {
  const int prot = PROT_READ | PROT_WRITE;
  const int flags = MAP_ANONYMOUS | MAP_SHARED;
  shared = (Shared *) mmap (0, sizeof *shared, prot, flags, -1, 0);
}

Mobical::~Mobical () {
  if (shared)
    munmap (shared, sizeof *shared);
  if (mock_pointer)
    delete mock_pointer;
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
    } else if (!strcmp (argv[i], "-v"))
      verbose = true;
    else if (is_color_option (argv[i]))
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
    else if (!strcmp (argv[i], "--do-not-shrink") ||
             !strcmp (argv[i], "--do-not-shrink-at-all"))
      donot.shrink.atall = true;
    else if (!strcmp (argv[i], "--do-not-add-options") ||
             !strcmp (argv[i], "--do-not-add-options-before-shrinking"))
      donot.add = true;
    else if (!strcmp (argv[i], "--do-not-shrink-phases"))
      donot.shrink.phases = true;
    else if (!strcmp (argv[i], "--do-not-shrink-clauses"))
      donot.shrink.clauses = true;
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
    } else if (!strcmp (argv[i], "--bad-alloc")) {
      bad_alloc = true;
    } else if (!strcmp (argv[i], "--leak-alloc")) {
      leak_alloc = true;
#else
    } else if (!strcmp (argv[i], "--bad-alloc")) {
      die ("--bad-alloc requires memory fuzzing to be enabled at compile "
           "time");
    } else if (!strcmp (argv[i], "--leak-alloc")) {
      die ("--leak-alloc requires memory fuzzing to be enabled at compile "
           "time");
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
      die ("too many trace files specified: '%s', '%s' and '%s' (try '-h')",
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

  // If a seed and a file (in that order) are specified the file is actually
  // not an input file but an output file.  To streamline the code below
  // swap input and output here.
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

  if (!output_path && donot.execute)
    die ("can not use '--do-no-execute' without '<output>'");

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

  /*----------------------------------------------------------------------*/

  // Print banner.

  prefix ();
  terminal.magenta (1);
  fputs ("Model Based Tester for the CaDiCaL SAT Solver Library\n", stderr);
  terminal.normal ();
  prefix ();
  terminal.magenta (1);
  printf ("%s\n", copyright ());
  terminal.normal ();
  prefix ();
  terminal.magenta (1);
  printf ("%s\n", authors ());
  terminal.normal ();
  prefix ();
  terminal.magenta (1);
  printf ("%s\n", affiliations ());
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

  prefix ();
  if (mobical.add_plain_after_options)
    cerr << "generating only plain instances (--plain)" << endl << flush;

  /*----------------------------------------------------------------------*/

  // Report mode.

  if (mode & RANDOM) {
    prefix ();
    if (limit >= 0)
      cerr << "randomly generating " << limit << " traces" << endl;
    else {
      cerr << "randomly generating traces";
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

  /*----------------------------------------------------------------------*/

  Signal::set (this);

  int res = 0;

  if (mode & (SEED | INPUT)) { // trace given through input or seed

    prefix ();
    cerr << right << setw (58) << "";
    header ();
    cerr << endl;
    hline ();

    Trace trace;

    if (seed_str) { // seed

      prefix ();
      cerr << left << setw (13) << "seed:";
      assert (is_unsigned_str (seed_str));
      uint64_t seed = parse_seed (seed_str);
      terminal.green ();
      cerr << setfill ('0') << right << setw (20) << seed;
      terminal.normal ();
      cerr << setfill (' ') << setw (24) << "";
      Trace::generated++;

      trace.generate (0, seed);

    } else { // input

      Reader reader (*this, trace, input_path);
      reader.parse ();

      prefix ();
      cerr << left << setw (13) << "input: ";
      assert (input_path);
      cerr << left << setw (44) << input_path;
    }

    cerr << ' ';
    summarize (trace);
    cerr << endl << flush;

    if (output_path) {

      if (!donot.execute) {

        res = trace.fork_and_execute ();
        if (res) {
          res = trace.fork_and_execute ();
          if (!res)
            spurious++;
        }

        if (res) {

          terminal.cursor (false);

          Trace::failed++;
          trace.shrink (res); // shrink
          if (!verbose && !terminal)
            cerr << endl;
          else
            terminal.erase_line_if_connected_otherwise_new_line ();

        } else
          Trace::ok++;
      }

      prefix ();
      cerr << left << setw (13) << "output:";

      trace.write_path (output_path); // output

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

    } else {
      trace.execute (); // execute
      Trace::ok++;
    }

  } else { // otherwise generate random traces forever

    Random random; // initialized by time and machine id

    if (seed_str) {
      uint64_t seed = parse_seed (seed_str);
      terminal.green ();
      random = seed;
    }

    prefix ();
    cerr << "start seed ";
    terminal.green ();
    cerr << random.seed ();
    terminal.normal ();
    cerr << endl;
    empty_line ();

    if (limit < 0)
      limit = LONG_MAX;

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

    for (traces = 1; traces <= limit; traces++) {

      if (!donot.seeds) {
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

      if (!donot.seeds) {
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

      if (!donot.seeds)
        terminal.erase_line_if_connected_otherwise_new_line ();

      if (res) { // failed

        prefix ();
        cerr << ' ' << left << setw (11) << traces << ' ';
        terminal.red ();
        trace.write_prefixed_seed ("bug"); // output
        terminal.normal ();
        cerr << setw (15) << "";
        summarize (trace);
        if (terminal)
          cerr << endl << flush;
        running = false;

        if (!donot.shrink.atall) {
          trace.shrink (res); // shrink
          if (!terminal && !verbose)
            cerr << endl;
          else
            terminal.erase_line_if_connected_otherwise_new_line ();
        }

        prefix ();
        cerr << ' ' << left << setw (11) << traces << ' ';

        terminal.red (true);
        trace.write_prefixed_seed ("red"); // output
        terminal.normal ();
        cerr << setw (15) << "";
        summarize (trace, true);
        cerr << endl << flush;
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
