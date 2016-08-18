#!/bin/sh
CXX="`sed -e '/^CXX=/!d' -e 's,.*=,,' makefile`"
CXXFLAGS="`sed -e '/^CXXFLAGS=/!d' -e 's,.*=,,' makefile`"
echo "#define VERSION \"`cat VERSION`\""
echo "#define COMPILE \"$CXX $CXXFLAGS\""
echo "#define GITID \"`./getgitid.sh`\""
