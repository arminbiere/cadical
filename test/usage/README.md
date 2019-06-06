These are some simple hard coded usage tests of the `cadical` solver binary
executed by `run.sh` which actually needs to be called from an immediate
sub-directory of CaDiCaL (such as the directory `..` one level up).  Log and
proof files are saved in the build directory.

The `makefile` allows to execute the CNF tests from within this
sub-directory with a single `make` command, but always uses `cadical`
from `../../build/` and also puts the log and error files there.
