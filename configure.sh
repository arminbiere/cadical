#!/bin/sh
debug=no
logging=no
check=no
profile=no
die () {
  echo "*** configure.sh: $*" 1>&2
  exit 1
}
usage () {
cat << EOF
usage: configure.sh [ <option> ... ]
where '<option>' is one of the following
-h|--help     print this command line summary
-g|--debug    compile with debugging information
-c|--check    compile with assertion checking (default for '-g')
-l|--log      include and enable logging code
-p|--profile  include and enable profiling code
-a|--all      short cut for '-g -l -p'
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
    -p|--profile) profile=yes;;
    -a|--all) debug=yes;check=yes;logging=yes;profile=yes;;
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
[ $profile = yes ] && CXXFLAGS="$CXXFLAGS -DPROFILE"
echo "$CXX $CXXFLAGS"
rm -f makefile
sed -e "s,@CXX@,$CXX," -e "s,@CXXFLAGS@,$CXXFLAGS," makefile.in > makefile
