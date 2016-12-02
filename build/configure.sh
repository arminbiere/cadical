#!/bin/sh
debug=no
stats=no
logging=no
check=no
coverage=no
profile=no

bce=no
shrink=no
backward=no

die () {
  echo "*** configure.sh: $*" 1>&2
  exit 1
}
[ -f ../VERSION -a -f makefile.in -a -f make-config-header.sh ] || \
die "change to 'build' directory before calling this script"
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
--bce        include BCE code
--shrink     include learned clause shrinking code
--backward   include eager backward subsumption code
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
    --bce) bce=yes;;
    --shrink) shrink=yes;;
    --backward) backward=yes;;
    --coverage) coverage=yes;;
    --profile) profile=yes;;
    *) die "invalid option '$1' (try '-h')";;
  esac
  shift
done
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
[ $bce = yes ] && CXXFLAGS="$CXXFLAGS -DBCE"
[ $shrink = yes ] && CXXFLAGS="$CXXFLAGS -DSHRINK"
[ $backward = yes ] && CXXFLAGS="$CXXFLAGS -DBACKWARD"
[ $profile = yes ] && CXXFLAGS="$CXXFLAGS -pg"
[ $coverage = yes ] && CXXFLAGS="$CXXFLAGS -ftest-coverage -fprofile-arcs"
echo "$CXX $CXXFLAGS"
rm -f makefile
sed -e "s,@CXX@,$CXX," -e "s,@CXXFLAGS@,$CXXFLAGS," makefile.in > makefile
