These are CNF files tested with `run.sh` which actually needs to be called
from an immediate sub-directory of CaDiCaL (such as the directory `..` one
level up).  Log and proof files are saved in the build directory.

The `.cnf` files are in DIMACS format.

The corresponding `.sol` files are in SAT competition output format and
provide pre-computed solutions for testing and debugging.

The tool `precochk.c` is used to check witness generated and saved in the
`.log` files in the build directory to be correct.

The tool `drat-trim.c` is used to check proofs generated and saved in the
`.prf` files in the build directory to be correct.

We are also testing the `simplifier` flow of CaDiCaL using the scripts

    ../../scripts/run-simplifier-and-extend-solution.sh
    ../../scripts/extend-solution.sh

The `makefile` allows to execute the CNF tests from within this
sub-directory with a single `make` command, but always uses `cadical`
from `../../build/` and also puts the log and error files there.
