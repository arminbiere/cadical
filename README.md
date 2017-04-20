# CaDiCaL

CaDiCaL Simplified Satisfiability Solver

The goal of the development of CaDiCaL is to obtain a CDCL solver, which is
easy to understand and change, while at the same time not being much slower
than other state-of-the-art CDCL solvers.  Originally we wanted to also
radically simplify the design and internal data structures, but that goal
only achieved partially, for instance compared to Lingeling.

Use './configure && make' to configure and build 'cadical' in the default
'build' sub-directory.  This will also build the library 'libcadical.a'.
  
  - ./build/libcadical.a

  - ./build/cadical

The default build process requires GNU make but simply issuing

  - cd src; g++ -O3 -DNDEBUG -o ../build/cadical \*.cpp

gives you a stand alone binary.  Using the generated 'makefile' with
GNU make compiles separate object files, which can be cached, and also can
be parallelized.

The header file of the library is in 'src/cadical.hpp'.

You might want to check out options of './configure -h', such as

  - ./configure -c # include assertion checking code

  - ./configure -l # include code to really see what the solver is doing

  - ./configure -a # both above and in addition '-g' for debugging.

The latest version of CaDiCaL can be found on 'github'

  - http://github.com/arminbiere/cadical

which also contains a test suite (use './run-regression.sh').

A plain stable source release will eventually be found at

  - http://fmv.jku.at/cadical

Armin Biere

Do 20. Apr 09:11:03 CEST 2017
