[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Build Status](https://travis-ci.com/arminbiere/cadical.svg?branch=master)](https://travis-ci.com/arminbiere/cadical)


CaDiCaL Simplified Satisfiability Solver
===============================================================================

The goal of the development of CaDiCaL was to obtain a CDCL solver,
which is easy to understand and change, while at the same time not being
much slower than other state-of-the-art CDCL solvers.

Originally we wanted to also radically simplify the design and internal data
structures, but that goal was only achieved partially, at least for instance
compared to Lingeling.

However, the code is much better documented and CaDiCaL actually became in
general faster than Lingeling even though it is missing some preprocessors
(mostly parity and cardinality constraint reasoning), which would be crucial
to solve certain instances.

Use `./configure && make` to configure and build `cadical` and the library
`libcadical.a` in the default `build` sub-directory.  The header file of
the library is [`src/cadical.hpp`](src/cadical.hpp) and includes an example
for API usage.
  
See [`BUILD.md`](BUILD.md) for options and more details related to the build
process and [`test/README.md`](test/README.md) for testing the library and
the solver.  Since release 1.5.1 we have a [`NEWS.md`](NEWS.md) file.

The solver has the following usage `cadical [ dimacs [ proof ] ]`.
See `cadical -h` for more options.

If you want to cite CaDiCaL please use the solver description in the
latest SAT competition proceedings:

<pre>
  @inproceedings{BiereFazekasFleuryHeisinger-SAT-Competition-2020-solvers,
    author    = {Armin Biere and Katalin Fazekas and Mathias Fleury and Maximillian Heisinger},
    title     = {{CaDiCaL}, {Kissat}, {Paracooba}, {Plingeling} and {Treengeling}
		 Entering the {SAT Competition 2020}},
    pages     = {51--53},
    editor    = {Tomas Balyo and Nils Froleyks and Marijn Heule and 
		 Markus Iser and Matti J{\"a}rvisalo and Martin Suda},
    booktitle = {Proc.~of {SAT Competition} 2020 -- Solver and Benchmark Descriptions},
    volume    = {B-2020-1},
    series    = {Department of Computer Science Report Series B},
    publisher = {University of Helsinki},
    year      = 2020,
  }
</pre>

You might also find more information on CaDiCaL at <http://fmv.jku.at/cadical>.

Armin Biere
