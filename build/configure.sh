#!/bin/sh

# Run './configure.sh' to produce a 'makefile' in the 'build' directory.

#--------------------------------------------------------------------------#
# Common default options.
#
debug=no
stats=no
logging=no
check=no
coverage=no
profile=no

#--------------------------------------------------------------------------#

die () {
  echo "*** configure.sh: $*" 1>&2
  exit 1
}

# Check that we are in the 'build' directory.

[ -f ../VERSION -a -f makefile.in -a -f make-config-header.sh ] || \
die "change to 'build' directory before calling this script"

#--------------------------------------------------------------------------#

# Parse and handle command line options.

usage () {
cat << EOF
usage: configure.sh [ <option> ... ]

where '<option>' is one of the following

-h|--help    print this command line summary
-g|--debug   compile with debugging information
-c|--check   compile with assertion checking (default for '-g')
-l|--log     include logging code (but disabled by default)
-s|--sats    include and enable expensive statistics code
-a|--all     short cut for all above, e.g., '-g -l -s' (thus also '-c')
--coverage   compile with '-ftest-coverage -fprofile-arcs' for 'gcov'
--profile    compile with '-pg' to profile with 'gprof'
EOF
exit 0
}

while [ $# -gt 0 ]
do
  case $1 in
    -h|--help) usage;;
    -g|--debug) debug=yes; check=yes;;
    -c|--check) check=yes;;
    -l|--logging) logging=yes;;
    -s|--stats) stats=yes;;
    -a|--all) debug=yes;check=yes;logging=yes;stats=yes;;
    --coverage) coverage=yes;;
    --profile) profile=yes;;
    *) die "invalid option '$1' (try '-h')";;
  esac
  shift
done

#--------------------------------------------------------------------------#

# Prepare '@CXX@' and '@CXXFLAGS@' parameters for 'makefile.in'

[ x"$CXX" = x ] && CXX=g++
if [ x"$CXXFLAGS" ]
then
  case x"$CXX" in
    xg++*|xclang++*) CXXFLAGS="-Wall";;
    *) CXXFLAGS="-W";;
  esac
  if [ $debug = yes ]
  then
    CXXFLAGS="$CXXFLAGS -g"
  else
    case x"$CXX" in
      xg++*|xclang++*) CXXFLAGS="$CXXFLAGS -O3";;
      *) CXXFLAGS="$CXXFLAGS -O";;
    esac
  fi
fi

[ $check = no ] && CXXFLAGS="$CXXFLAGS -DNDEBUG"
[ $logging = yes ] && CXXFLAGS="$CXXFLAGS -DLOGGING"
[ $stats = yes ] && CXXFLAGS="$CXXFLAGS -DSTATS"
[ $profile = yes ] && CXXFLAGS="$CXXFLAGS -pg"
[ $coverage = yes ] && CXXFLAGS="$CXXFLAGS -ftest-coverage -fprofile-arcs"

#--------------------------------------------------------------------------#

# Instantiate the 'makefile.in' template to produce 'makefile'.

echo "$CXX $CXXFLAGS"
rm -f makefile
sed -e "s,@CXX@,$CXX," -e "s,@CXXFLAGS@,$CXXFLAGS," makefile.in > makefile
