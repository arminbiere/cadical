Version 2.1.3
-------------

- New interface to support propagation of assumptions. The following functions
are available now:

  + `propagate ()`: Applies unit propagation on the assumptions given to the
    solver previously (supposed to be called instead of `solve ()`).

  + `get_entrailed_literals (std::vector<int> &)`: In case `propagate ()`
    returned `0` (UNKNOWN), this function returns (the subset of) those
    literals that were assigned based on the assumptions and propagation.
    Those assigned literals that are tainted on the reconstruction stack
    (due to some preprocessing) are not returned, thus it is safe to 
    combine it with the formula simplifications.

- LIDRUP proofs now include information about queries that returned with
  UNKNOWN result.


Version 2.1.2
-------------

- Fixed version number.

- Reentrant multi-threaded writing of compressed files fixed
  with 'closeform' (using 'pipe|fork|exec|closefrom') on Linux.

- New IPASIR-UP options, with the same default as in 1.1:

   + `exteagerreasons` where the solver eagerly asks for reasons before
     analysing conflicts instead of being lazy (default: eager)

   + `exteagerrecalc` where the solver recalculates the levels on the
     trail before conflict analysis (default: on). Mostly useful if
     the solver provides many propagations in a lazy fashion. Requires
     `exteagerreasons` to be on to have any effect.

- Fix performance regression for incremental SAT solving due to too
  eager garbage collection before any incremental call in favor of
  only doing it during variable elimination

- Fix performance regression for the SAT anniversary track.

- Slight memory usage reduction expected thanks to not allocating some
  internal array only used for proof and external propagator.

- Mobical deterministic compiled with or without logging.

- Fixed memory corruption and leaks when allocation of arena fails
  and further added support in fuzzer to trigger such bad allocations.

Version 2.1.0
-------------

- Major IPASIR-UP increment. Please be aware that some of these
  changes affect the syntax of the API, and thus updating to this
  version of CaDiCaL requires to modify the consuming code to 
  accommodate to the new syntax:

  - Notification of assignments is batched into arrays and no more fixed
    flags are passed during notification (`breaking change`)
  
  - Allow clauses learned from the propagator to be deleted (see
    `is_forgettable` parameter and `are_reasons_forgettable` Boolean flag)
    (`breaking change`)
  
  - Added support to generate incremental proofs (LIDRUP) while 
    using IPASIR-UP

  - Users can force to backtrack during `cb_decide` (see function
    `force_backtrack`)
  
  - Removed unnecessary notifications of backtrack during
    inprocessing (supposed to solve issue #92).

  - Call again `cb_propagate` if during final model checking a new
    clause is added.

- Added a new interface `FixedAssignmentListener`: Eagerly calls a
  callback whenever a variable is fixed during search.

Version 2.0.0
-------------

- We have now a `contrib` directory and for starters there our
  `CadiCraig` interpolator, which goes through the `Tracer` API.

- We moved back to use the C99 flexible array member feature in
  `Clause` which however is not supported by all C++ compiler
  configurations, particularly if compiling in pedantic mode.
  Therefore the `configure` script checks for support of flexible
  array members and also has a new `--no-flexible` option.

- Added `Dockerfile` to support docker containers.

- Added `--no-status` to skip printing "s SATISFIABLE" or "s
  UNSATISFIABLE". This is useful for online proof checking.

Version 1.9.5
-------------

- Removed an unexpected performance regression on the anniversary track
  due to marking forward strengthened redundant clauses as used.

Version 1.9.4
-------------

- Simplified code by removing reimply again (but keeping ILB).

Version 1.9.3
-------------

- Fixed bogus notification if a user propagator is connected
  with ILB and after local search preprocessing and a second incremental
  call lead to an inconsistent trail to assumption mapping, which might
  have lead to an infinite loop (in very rare cases).

Version 1.9.2
-------------

- Important fixes for ILB, trail-reuse and external propagation with
  assumptions.

- Restored effectiveness of Mobical and improved external mock
  propagator.

- Forced garbage collection of binary clauses before restore.

- Merge internal status and state encodings and made them consistent.

- Disabled non-verbose message if empty clause found in input.

- Improved support for IDRUP.

Version 1.9.1
-------------

- Fixed position of `idrup` option.

Version 1.9.0
-------------

- Clause IDs in binary LRAT proofs are now always signed.

- Internal CNF regression suite also checks LRAT proofs now.

- Improving the OTFS heuristic (properly bumping literals and
  considering that the conflict clause is updated).

- Making progress to formal 1.9 release with minor fixes for
  different platforms and compilers.

- Refine IPASIR-UP based on feedback from users. 

Version 1.8.0
-------------

- Explicit `Solver::clause` functions to simplify clause addition.

- More fine-grained handling of printing proof size information by
  adding `bool print = false` flags to the `flush_proof_trace` and
  the `close_proof_trace` API calls.  The former prints the number
  of addition and deletion steps, while the latter prints the size
  of the proof size (and the actual number of bytes if compressed).
  The main effect is that by default printing of proof size disabled
  for API usage but enabled for the stand-alone solver.

Version 1.7.5
-------------

- Decreased verbosity level for printing proof size.

Version 1.7.4
-------------

- As `fork` and `wait` do not exist on Windows writing compressed files
  through `pipe/fork/exec/wait` has to be disabled for Windows cross
  compilation to go through.  Alternatively one could go back to `popen`
  for writing compressed files on Windows which however is not safe and
  therefore we simply decided to disable that feature for windows.
  Compressed file reading still (and as far we are aware safely) uses
  `popen` and thus also compiles for Windows.

Version 1.7.3
-------------

- Replaced the unsafe `popen` approach for compressed file writing
  with an explicit `pipe/fork/exec/waitpid` flow and accordingly
  removed the `--safe` configuration option again.

- Incremental lazy backtracking (ILB) enabled by `--ilb` allows
  to add new clauses incrementally while keeping the assignments
  on the trail.  Also works for assumptions (`--ilbassumptions`).

- Reimplication (`--reimply`) fixes assignment levels of literals by
  "elevating" them (assigning a lower decision level and propagating them
  out-of-order on this lower decision level).  Out-of-order assignments are
  introduced by chronological backtracking, adding external clauses during
  solving (e.g., by a user propagation) or simply by ILB.  Reimplication
  improves quality of learned clauses and potentially shortens search in
  such cases.
 
- A new proof tracer interface allows to add a proof `Tracer` through the
  API (via `connect_proof_tracer`). This feature allows to use custom
  proof tracers to process clausal proofs on-the-fly while solving.  Both
  proofs steps with proof antecedents (needed for instance for
  interpolation) as well as without (working directly on DRAT level) are
  supported.
 
- Reworked options for proof tracing to be less confusing.  Support for
  DRAT, LRAT, FRAT and VeriPB (with or without antecedents).

Version 1.7.2 -------------

- Configuration option `--safe` disables writing to a file through `popen`
  which makes library usage safer.

Version 1.7.1 -------------

- Added support for VeriPB proofs (--lrat --lratveripb).

- Various fixes: LRAT proofs for constrain (which previously were not traced
  correctly); internal-external mapping issues for LRAT (worked for user
  propagator but now also in combination with LRAT); further minor bug
  fixes.

- Added support for LRAT + external propagator in combination.

Version 1.7.0 -------------

- Added native LRAT support.

Version 1.6.0 -------------

- Added IPASIR-UP functions to the API to support external propagation,
  external decisions, and clause addition during search.  For more details
  see the following paper at SAT 2023:

 Katalin Fazekas, Aina Niemetz, Mathias Preiner, Markus Kirchweger, Stefan
 Szeider and Armin Biere. IPASIR-UP: User Propagators for CDCL.

- During decisions the phase set by `void phase (int lit)` has now higher
  precedence than the initial phase set by options `phase` and `forcephase`.

Version 1.5.6 -------------

- Clang formatted all source code (and fixed one failing regression test by
  disabling `otfs` for it).

- Implementing OTFS during conflict analysis (`--otfs`).

- The last literal set by vivification is instantiated (`--vivifyinst`).

- More accurate tracking of binary clauses in watch lists by updating the
  size in watch lists.

Version 1.5.4 -------------

- Picking highest score literal in assumed clause (`constrain`) and caching
  of satisfied literal by moving them to the front.

- Added `bool flippable (int lit)` to API.

- Fixed `val` to return `lit` or `-lit` and not just `-1` and `1`.

- Allowing `fixed` between `constrain` in `mobical`.

- Fixed LZMA magic header.

- Added `bool flip (int lit)` to API.

- Fixed different garbage collection times with and without clause IDs (with
  `./configure -l` or just `./configure`).  This solves issue #44 by John
  Reeves.  At the same time made sure to trigger garbage collection
  independent on the number of clause header bytes by relying on the number
  of garbage literals instead.

- Fixed `mmap` usage for FreeBSD (#48 issue of `yurivict`).

- Removed several compiler warnings when using newer compilers, including
  gcc-11, gcc-12, clang-14, and clang-15.

- Replaced `sprintf` by `snprintf` to avoid warning on MacOS (thanks to
  Marijn for bringing this up).

- Assigning a C `FILE` pointer to `stdout` during initialization fails on
  MacOS and thus separated declaration and initialization.

- Fixed random seed initialization from MAC address issue #47 as used by
  `mobical` which produces segmentation faults (thanks to Sam Bayless for
  pointing this out).

Version 1.5.2 -------------

- Updates to documentation and copyright.

Version 1.5.2 -------------

- More copyright updates in banner.

- Fixed MinGW cross-compilation (see `BUILD.md`).

Version 1.5.1 -------------

- Fixed copyright and added two regression traces.

Version 1.5.0 -------------

- Added `constrain` API call described in our FMCAD'21 paper.

- Replaced `while () push_back ()` with `if () resize ()` idiom (thanks go
  to Alexander Smal for pointing this out).
