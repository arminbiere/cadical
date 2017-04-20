#!/bin/sh

# Used to 'config.hpp', which in turn is used in 'banner' to print compile
# time options, compiler version, and source code version.

# Otherwise might have for instance an umlaut in 'CADICAL_COMPILED'
#
LC_TIME="en_US"
export LC_TIME

# Get compiler, its versions and compile flags from 'makefile'.
#
CXX="`sed -e '/^CXX=/!d' -e 's,.*=,,' makefile`"
CXXFLAGS="`sed -e '/^CXXFLAGS=/!d' -e 's,.*=,,' makefile`"
case x"$CXX" in 
  xg++* | xclang++*) CXXVERSION="`$CXX --version|head -1`";;
  *) CXXVERSION="unknown compiler version";;
esac

# The current version number.
echo "#define CADICAL_VERSION \"`cat ../VERSION`\""

# The unique GIT hash.
echo "#define CADICAL_GITID \"`../scripts/get-git-id.sh`\""

# The C++ compiler as used in the current 'makefile'.
echo "#define CADICAL_CXX \"$CXX\""

# Compile flags as used in the current 'makefile'.
echo "#define CADICAL_CXXFLAGS \"$CXXFLAGS\""

# The version of the compiler (currently works only for 'g++' and 'clang++')
echo "#define CADICAL_CXXVERSION \"$CXXVERSION\""

# The time and date we compiled the CaDiCaL library.
echo "#define CADICAL_COMPILED \"`date`\""

# The operating system on which this compilation took place.
echo "#define CADICAL_OS \"`uname -srmn`\""
