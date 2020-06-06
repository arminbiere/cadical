This is the source code of the library `libcadical.a` with header
`cadical.hpp`, the stand-alone solver `cadical` (in `cadical.cpp`) and the
model based tester `mobical` (in `mobical.app`).

The `configure` script and link to the `makefile` in the root directory
can be used from within the `src` sub-directory too and then will just work
as if used from the root directory.  For instance

    ./configure && make test

will configure and build in `../build` the default (optimizing)
configuration and if successful then run the test suite.
