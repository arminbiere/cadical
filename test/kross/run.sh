#!/bin/sh
#--------------------------------------------------------------------------#

die () {
  cecho "${HIDE}test/kross/run.sh:${NORMAL} ${BAD}error:${NORMAL} $*"
  exit 1
}

msg () {
  cecho "${HIDE}test/kross/run.sh:${NORMAL} $*"
}

for dir in . .. ../..
do
  [ -f $dir/scripts/colors.sh ] || continue
  . $dir/scripts/colors.sh || exit 1
  break
done

#--------------------------------------------------------------------------#

[ -d ../test -a -d ../test/kross ] || \
die "needs to be called from a top-level sub-directory of CaDiCaL"

[ x"$CADICALBUILD" = x ] && CADICALBUILD="../build"

[ -f "$CADICALBUILD/makefile" ] || \
  die "can not find '$CADICALBUILD/makefile' (run 'configure' first)"

[ -f "$CADICALBUILD/libcadical.a" ] || \
  die "can not find '$CADICALBUILD/libcadical.a' (run 'make' first)"

exit_if_not_a_directory () {
  if [ ! -d "$1" ]
  then
    msg "no '$1' directory (skipping cross testing against 'Kissat')"
    exit 0
  fi
}

exit_if_not_a_file () {
  if [ ! -f "$1" ]
  then
    msg "could not find '$1' (skipping cross testing against 'Kissat')"
    exit 0
  fi
}

kissatdir="$CADICALBUILD/../../kissat"
kissatbuild="$kissatdir/build"
kissatlib="$kissatdir/build/libkissat.a"
kissatsrc="$kissatdir/src"
kissatheader="$kissatsrc/kissat.h"

exit_if_not_a_directory "$kissatdir"
exit_if_not_a_directory "$kissatbuild"
exit_if_not_a_file "$kissatlib"
exit_if_not_a_directory "$kissatsrc"
exit_if_not_a_file "$kissatheader"

cecho -n "$HILITE"
cecho "---------------------------------------------------------"
cecho "Cross testing in '$CADICALBUILD' with '$kissatdir'"
cecho "---------------------------------------------------------"
cecho -n "$NORMAL"

make -C $CADICALBUILD
res=$?
[ $res = 0 ] || exit $res

#--------------------------------------------------------------------------#

makefile=$CADICALBUILD/makefile

CXX=`grep '^CXX=' "$makefile"|sed -e 's,CXX=,,'`
CXXFLAGS=`grep '^CXXFLAGS=' "$makefile"|sed -e 's,CXXFLAGS=,,'`

msg "using CXX=$CXX"
msg "using CXXFLAGS=$CXXFLAGS"

exe=$CADICALBUILD/test-kross-kross1.exe 
set -ex

$CXX $CXXFLAGS \
  -o $exe \
  "-I../src" \
  "-I$kissatsrc" \
  ../test/kross/kross1.cpp \
  "-L$CADICALBUILD" \
  "-L$kissatbuild" \
  "-lcadical" \
  "-lkissat"

$exe

