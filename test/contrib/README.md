These are unit tests of the contributed code executed with `run.sh` which
actually needs to be called from an immediate sub-directory of CaDiCaL.

The binary and results of the tests are put into the build directory.

The `makefile` allows to compile and execute the tests from within this
sub-directory with a single `make` command, but then uses `../../build` as
build directory.
