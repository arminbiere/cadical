Version 1.6.0
-------------

  - Added IPASIR-UP functions to the API to support external propagation,
    external decisions, and clause addition during search.
    For more details see the following paper at SAT 2023:

    Katalin Fazekas, Aina Niemetz, Mathias Preiner, Markus Kirchweger,
    Stefan Szeider and Armin Biere. IPASIR-UP: User Propagators for CDCL.

  - During decisions the phase set by 'void phase (int lit)' has now
    higher precedence than the initial phase set by options 'phase' and
    'forcephase'.

Version 1.5.6
-------------

 - Clang formatted all source code (and fixed one failing regression
   test by disabling 'otfs' for it).

 - Implementing OTFS during conflict analysis (--otfs).

 - The last literal set by vivification is instantiated (--vivifyinst).

 - more accurate tracking of binary clauses in watch lists by updating
   the size in watch lists.

Version 1.5.4
-------------

- Picking highest score literal in assumed clause ('constrain')
  and caching of satisfied literal by moving them to the front.

- Added 'bool flippable (int lit)' to API.

- Fixed 'val' to return 'lit' or '-lit' and not just '-1' and '1'.

- Allowing 'fixed' between 'constrain' in 'mobical'.

- Fixed LZMA magic header.

- Added 'bool flip (int lit)' to API.

- Fixed different garbage collection times with and without
  clause IDs (with './configure -l' or just './configure').
  This solves issue #44 by John Reeves.  At the same time
  made sure to trigger garbage collection independent on the
  number of clause header bytes by relying on the number of
  garbage literals instead.

- Fixed 'mmap' usage for FreeBSD (#48 issue of 'yurivict').

- Removed several compiler warnings when using newer compilers,
  including gcc-11, gcc-12, clang-14, and clang-15.

- Replaced 'sprintf' by 'snprintf' to avoid warning on MacOS
  (thanks to Marijn for bringing this up).

- Assigning a C 'FILE' pointer to 'stdout' during initialization
  fails on MacOS and thus separated declaration and initialization.

- Fixed random seed initialization from MAC address issue #47
  as used by 'mobical' which produces segmentation faults
  (thanks to Sam Bayless for pointing this out).

Version 1.5.2
-------------

- Updates to documentation and copyright.

Version 1.5.2
-------------

- More copyright updates in banner.

- Fixed MinGW cross-compilation (see 'BUILD.md').

Version 1.5.1
-------------

- Fixed copyright and added two regression traces.

Version 1.5.0
-------------

- Added 'constrain' API call described in our FMCAD'21 paper.

- Replaced "`while () push_back ()`" with "`if () resize ()`" idiom
  (thanks go to Alexander Smal for pointing this out).
