# CaDiCaL
Radically Simplified Conflict Driven Clause Learning Solver (CDCL)

The goal of CaDiCal is to have a minimalistic CDCL solver,
which is easy to understand and change, while at the same
time not too much slower than state of the art CDCL solvers
if pre-processing is disabled.

Run './configure.sh' and then 'make' to compile 'cadical'.

You might want to check out options of './configure.sh -h', such as

  ./configure -p # to measure time spent in functions
  ./configure -l # to really see what the solver is doing
  ./configure -a # both above and in addition '-g' for debugging.

The lastest version of CaDiCal can be found on 'github'

  http://github.com/arminbiere/cadical

which also contains a test suite (run './run-regression.sh').

A plain stable source release can be found on

  http://fmv.jku.at/cadical

Armin Biere
Do 25. Aug 02:26:08 CEST 2016
