# CaDiCaL Build

Use `./configure && make` to configure and build `cadical` in the default
`build` sub-directory.

This will also build the library `libcadical.a` as well as the model based
tester `mobical`:
  
    build/cadical
    build/mobical
    build/libcadical.a

The header file of the library is in

    src/cadical.hpp

The build process requires GNU make.  Using the generated `makefile` with
GNU make compiles separate object files, which can be cached (for instance
with `ccache`).  In order to force parallel build you can use the '-j'
option either for 'configure' or with 'make'.  If the environment variable
'MAKEFLAGS' is set, e.g., 'MAKEFLAGS=-j ./configure', the same effect
is achieved and the generated makefile will use those flags.

Options
-------

You might want to check out options of `./configure -h`, such as

    ./configure -c # include assertion checking code

    ./configure -l # include code to really see what the solver is doing

    ./configure -a # both above and in addition `-g` for debugging.

You can easily use multiple build directories, e.g.,

    mkdir debug; cd debug; ../configure -g; make

which compiles and builds a debugging version in the sub-directory `debug`,
since `-g` was specified as parameter to `configure`.  The object files,
the library and the binaries are all independent of those in the default
build directory `build`.

All source files reside in the `src` directory.  The library `libcadical.a`
is compiled from all the `.cpp` files except `cadical.cpp` and
`mobical.cpp`, which provide the applications, i.e., the stand alone solver
`cadical` and the model based tester `mobical`.

Manual Build
------------

If you can not or do not want to rely on our `configure` script nor on our
build system based on GNU `make`, then this is easily doable as follows.

    mkdir build
    cd build
    for f in ../src/*.cpp; do g++ -O3 -DNDEBUG -DNBUILD -c $f; done
    ar rc libcadical.a `ls *.o | grep -v ical.o`
    g++ -o cadical cadical.o -L. -lcadical
    g++ -o mobical mobical.o -L. -lcadical

Note that application object files are excluded from the library.
Of course you can use different compilation options as well.
  
Since `build.hpp` is not generated in this flow the `-DNBUILD` flag is
necessary though, which avoids dependency of `version.cpp` on `build.hpp`.
Consequently you will only get very basic version information compiled into
the library and binaries (guaranteed is in essence just the version number
of the library).

And if you really do not care about compilation time nor caching and just
want to build the solver once manually then the following also works.

    g++ -O3 -DNDEBUG -DNBUILD -o cadical `ls *.cpp | grep -v mobical`

Further note that the `configure` script provides some feature checks and
might generate additional compiler flags necessary for compilation.  You
might need to set those yourself or just use a modern C++11 compiler.

This manual build process using object files is fast enough in combination
with caching solutions such as `ccache`.  But it lacks the ability of our
GNU make solution to run compilation in parallel without additional parallel
process scheduling solutions.

Cross-Compilation
-----------------

We have preliminary support for cross-compilation using MinGW32 (only
tested for a Linux compilation host and Windows-64 target host at this
point).

There are two steps necessary to make this work.  First make
sure to be able to execute binaries compiled with the cross-compiler
directly.  Otherwise 'configure' does not work automatically and you
have to build manually (as described above).

For instance in order to use `wine` to execute the binaries first install
`wine` which for instance on Ubuntu just requires

    sudo apt install wine

Then on Linux you might want to look into the `binfmt_misc` module and
as root register the appropriate interpreter for `DOSWin`.

    cd /proc/sys/fs/binfmt_misc
    echo ':DOSWin:M::MZ::/usr/bin/wine:' > register

Finally simply tell the `configure` script to use the cross-compiler.

    CXX=i686-w64-mingw32-g++ ./configure -static -lpsapi && make cadical

Note the use of '-static', which was necessary for me since by default
`wine` did not find `libstdc++` if dynamically linked.  There is also
a dependency on the 'psapi' library. Also `mobical` does not compile with
MinGW32 due to too many Unix dependencies and thus only make 'cadical'.
