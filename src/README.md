The 'configure' script and the 'makefile' are just proxies to those in the
root directory.  They can be used from within the 'src' sub-directory too
and then will just work as if used from the root directory.  Thus

  ./configure && make test

Will configure and build in '../build' the default (optimizing)
configuration and then also run the test suite.
