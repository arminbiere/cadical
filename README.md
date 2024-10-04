[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)


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
You might also want to check out [`CONTRIBUTING.md`](CONTRIBUTING.md) on
if you want to contribute.

The solver has the following usage `cadical [ dimacs [ proof ] ]`.
See `cadical -h` for more options.

If you want to cite CaDiCaL please use as reference our CaDiCaL 2.0 tool
paper which appeared at CAV'24:

<p>
<a
href="https://cca.informatik.uni-freiburg.de/papers/BiereFallerFazekasFleuryFroleyksPollitt-CAV24.pdf">CaDiCaL
2.0</a>
<br>
<a href="https://cca.informatik.uni-freiburg.de/biere">Armin Biere</a>,
<a href="https://cca.informatik.uni-freiburg.de/fallert">Tobias Faller</a>,
<a href="https://kfazekas.github.io">Katalin Fazekas</a>,
<a href="https://cca.informatik.uni-freiburg.de/fleury">Mathias Fleury</a>,
<a href="https://fmv.jku.at/froleyks">Nils Froleyks</a> and
<a href="https://cca.informatik.uni-freiburg.de/pollittf">Florian Pollitt</a>
<br>
<i>
Proc.&nbsp;Computer Aidded Verification - 26th Intl.&nbsp;Conf.&nbsp;(CAV'24)</i>
<br>
Lecture Notes in Computer Science (LNCS)
<br>
vol.&nbsp;14681,
pages 133-152,
Springer 2024
<br>
[ <a href="https://cca.informatik.uni-freiburg.de/papers/BiereFallerFazekasFleuryFroleyksPollitt-CAV24.pdf">paper</a>
| <a href="https://cca.informatik.uni-freiburg.de/papers/BiereFallerFazekasFleuryFroleyksPollitt-CAV24.bib">bibtex</a>
| <a href="https://cca.informatik.uni-freiburg.de/papers/BiereFallerFazekasFleuryFroleyksPollitt-CAV24-Springer.pdf">official</a>
| <a href="https://zenodo.org/records/10943125">artifact</a>
| <a href="https://github.com/arminbiere/cadical">github</a>
| <a href="https://doi.org/10.1007/978-3-031-37703-7">doi</a>
]
</p>
