# CaDiCaL

CaDiCaL Simplified Satisfiability Solver

The goal of the development of CaDiCaL is to provide a CDCL solver, which is
easy to understand and change, while at the same time not being much slower
than other state-of-the-art CDCL solvers.  Originally we wanted to also
radically simplify the design and internal data structures, but that goal
was only achieved partially.

First go to the 'build' subdirectory and then run './configure.sh',
followed by 'make'.  This will build the library and the executable
  
  - ./build/libcadical.a

  - ./build/cadical

The default build process requires GNU make but simply issuing

  - cd src; g++ -O3 -DNDEBUG -o ../build/cadical \*.cpp

should give you a stand alone binary.  Using the generated 'makefile' with
GNU make compiles seperate object files, which can be cached, and can be
parallelized (for instance by setting the environment variables CORES, e.g.,
using 'CORES=4 make' on a 4 core machine).

The header file of the library is in 'src/cadical.hpp'.

You might want to check out options of './configure.sh -h', such as

  - ./configure -p # to measure/profile time spent in functions

  - ./configure -l # to really see what the solver is doing

  - ./configure -a # both above and in addition '-g' for debugging.

The latest version of CaDiCaL can be found on 'github'

  - http://github.com/arminbiere/cadical

which also contains a test suite (use './run-regression.sh').

A plain stable source release can eventually be found at

  - http://fmv.jku.at/cadical

Armin Biere

Mit Nov 16 11:08:56 CET 2016
