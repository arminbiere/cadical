[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Build Status](https://travis-ci.com/arminbiere/cadical.svg?branch=master)](https://travis-ci.com/arminbiere/cadical)


CaDiCaL Simplified Satisfiability Solver
===============================================================================

The original goal of the development of CaDiCaL was to obtain a CDCL solver,
which is easy to understand and change, while at the same time not being
much slower than other state-of-the-art CDCL solvers.  Originally we wanted
to also radically simplify the design and internal data structures, but that
goal was only achieved partially, at least for instance compared to
Lingeling.

However, the code is much better documented and on the other hand CaDiCaL
actually became in general faster than Lingeling even though it is missing
some preprocessors (mostly parity and cardinality constraint reasoning),
which would be crucial to solve certain instances.

Use `./configure && make` to configure and build `cadical` and the library
`libcadical.a` in the default `build` sub-directory.  The header file of
the library is [`src/cadical.hpp`](src/cadical.hpp) and includes an example
for API usage.
  
See [`BUILD.md`](BUILD.md) for options and more details related to the build
process and [`test/README.md`](test/README.md) for testing the library and
the solver.

The solver has the following usage `cadical [ dimacs [ proof ] ]`.
See `cadical -h` for more options.

The latest version can be found at <http://fmv.jku.at/cadical>.

Armin Biere
