The tests can be executed by `make test` from a configured build,  the `src`
or `test` directory and will put their intermediate and log files in the
build directory.  If called from outside from the build directory the last
configured build directory is used.

We have four test drivers.  The simplest one

    ./api/run.sh

is going through the API directly to test basic stand-alone functionality of
the library.  Next is a simple usage test for all command line options.

    ./usage/run.sh

The regression suite for CNF files

    ./cnf/run.sh

is more thorough and should catch simple bugs.  It checks solutions and
checks generated proofs too.  The third test driver uses a regression suite
and executes traces by replaying them through `mobical`

    ./traces/run.sh

Last but not least the model based tester `../src/mobical.cpp` is the
most effective test driver and can be run through

    ./mbt/run.sh

All test drivers place their intermediate and logging files into the build
directory.  Thus if for instance you build in a `release` subdirectory
within the root directory of CaDiCaL

    mkdir release
    cd release
    ../configure
    make test

will use the library and binaries in this `release` sub-directory for
running all the tests.  The log files including generated proofs are all put
into the `release` subdirectory too.

For more information on external fuzz-testing see

> Robert Brummayer, Florian Lonsing, Armin Biere:
> Automated Testing and Debugging of SAT and QBF Solvers. SAT 2010: 44-57

Model based testing of SAT solvers is described in

> Cyrille Artho, Armin Biere, Martina Seidl:
> Model-Based Testing for Verification Back-Ends. TAP 2013: 39-55

The simple API test driver and the regression suite are executed by the
default goal of the `makefile`.  There is no need to clean up test output
since it is all put into the build directory.
