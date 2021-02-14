# CaDiCaL Scripts

Scripts needed for the build process

    ./make-build-header.sh   # generates 'build.hpp'
    ./get-git-id.sh          # get GIT id (needed by 'make-build-header.sh')
    ./update-version.sh      # synchronizes VERSION in '../src/version.cpp'

and a script which builds and tests all configurations

    ./build-and-test-all-configurations.sh
    CXX=clang++ ./build-and-test-all-configurations.sh
    CXX=g++-4.8 ./build-and-test-all-configurations.sh

where as the code shows the compiler (default `g++`) is specified through
the environment variable `CXX` (as for `../configure`).  Then there are
scripts for producing a source release

    ./make-src-release.sh          # archive as 'cadical-VERSION-GITID.tar.xz'
    ./prepare-sc2021-submission.sh # star-exec format for SAT competition

and scripts for testing and debugging

    ./generate-embedded-options-default-list.sh # in 'c --opt=val' format
    ./generate-options-range-list.sh            # 'cnfuzz' option file format
    ./run-cadical-and-check-proof.sh            # wrapper to check proofs too
    ./run-simplifier-and-extend-solution.sh     # to check simplifier
    ./extend-solution.sh                        # called by previous script

a script to check whether all options are actually used

    ./check-options-occur.sh

a script to update the example in the `../src/cadical.hpp` header

    ./update-example-in-cadical-header-file.sh

and finally a script to normalize white space of the source code

    ./normalize-white-space.sh

The `color.sh` script is used by the `run.sh` scripts in `test`.
