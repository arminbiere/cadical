# CaDiCaL

CaDiCaL Simplified Satisfiability Solver

The goal of the development of CaDiCaL is to obtain a CDCL solver, which is
easy to understand and change, while at the same time not being much slower
than other state-of-the-art CDCL solvers.  Originally we wanted to also
radically simplify the design and internal data structures, but that goal
was only achieved partially, for instance compared to Lingeling.

Use './configure && make' to configure and build 'cadical' in the default
'build' sub-directory.  This will also build the library 'libcadical.a'.
  
  - ./build/libcadical.a

  - ./build/cadical

The build process requires GNU make.  Using the generated 'makefile' with
GNU make compiles separate object files, which can be cached (for instance
with 'ccache').  The 'makefile' uses parallel compilation by default ('-j').

The header file of the library is in 'src/cadical.hpp'.

You might want to check out options of './configure -h', such as

  - ./configure -c # include assertion checking code

  - ./configure -l # include code to really see what the solver is doing

  - ./configure -a # both above and in addition '-g' for debugging.

You can easily use multiple build directories, e.g.,

  - mkdir debug; cd debug; ../configure -g; make

which compiles and builds a debugging version in the sub-directory 'debug',
since '-g' was specified as parameter to 'configure'.  The object files,
the library and the binary are all independent of those in the default
build directory 'build'.

The latest version of CaDiCaL can be found on 'github'

  - http://github.com/arminbiere/cadical

which also contains a test suite.  Use 'make test' to run it.

A plain stable source release will eventually be found at

  - http://fmv.jku.at/cadical

Armin Biere

Do 8. Jun 08:44:52 CEST 2017
