The model based tester binary `mobical` from the build directory is used to
generate a certain number of random API calls.  Generated original and
reduced error traces will go to the build directory.

The `run.sh` script is only used for `make test`.

The `makefile` allows to run this tests with a single `make`.
