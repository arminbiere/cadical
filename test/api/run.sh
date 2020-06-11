#!/bin/sh

#--------------------------------------------------------------------------#

die () {
  cecho "${HIDE}test/api/run.sh:${NORMAL} ${BAD}error:${NORMAL} $*"
  exit 1
}

msg () {
  cecho "${HIDE}test/api/run.sh:${NORMAL} $*"
}

for dir in . .. ../..
do
  [ -f $dir/scripts/colors.sh ] || continue
  . $dir/scripts/colors.sh || exit 1
  break
done

#--------------------------------------------------------------------------#

[ -d ../test -a -d ../test/api ] || \
die "needs to be called from a top-level sub-directory of CaDiCaL"

[ x"$CADICALBUILD" = x ] && CADICALBUILD="../build"

[ -f "$CADICALBUILD/makefile" ] || \
  die "can not find '$CADICALBUILD/makefile' (run 'configure' first)"

[ -f "$CADICALBUILD/libcadical.a" ] || \
  die "can not find '$CADICALBUILD/libcadical.a' (run 'make' first)"

cecho -n "$HILITE"
cecho "---------------------------------------------------------"
cecho "API testing in '$CADICALBUILD'"
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

tests=../test/api

export CADICALBUILD

#--------------------------------------------------------------------------#

ok=0
failed=0

cmd () {
  test $status = 1 && return
  cecho $*
  $* >> $name.log
  status=$?
}

run () {
  msg "running API test ${HILITE}'$1'${NORMAL}"
  if [ -f $tests/$1.c ]
  then
    src=$tests/$1.c
    language=" -x c"
    COMPILE="$CXX `echo $CXXFLAGS|sed -e 's,-std=c++0x,-std=c99,'`"
  elif [ -f $tests/$1.cpp ]
  then
    src=$tests/$1.cpp
    language=""
    COMPILE="$CXX $CXXFLAGS"
  else
    die "can not find '$tests.c' nor '$tests.cpp'"
  fi
  name=$CADICALBUILD/test-api-$1
  rm -f $name.log $name.o $name
  status=0
  cmd $COMPILE$language -o $name.o -c $src
  cmd $COMPILE -o $name $name.o -L$CADICALBUILD -lcadical
  cmd $name
  if test $status = 0
  then
    cecho "# 0 ... ${GOOD}ok${NORMAL} (zero exit code)"
    ok=`expr $ok + 1`
  else
    cecho "# 0 ... ${BAD}failed${NORMAL} (non-zero exit code)"
    failed=`expr $failed + 1`
  fi
}

#--------------------------------------------------------------------------#

run newdelete
run unit
run morenmore
run ctest
run example
run terminate
run learn
run cfreeze
run traverse
run cipasir

[ "`grep DNTRACING $makefile`" = "" ] && run apitrace

#--------------------------------------------------------------------------#

[ $ok -gt 0 ] && OK="$GOOD"
[ $failed -gt 0 ] && FAILED="$BAD"

msg "${HILITE}API testing results:${NORMAL} ${OK}$ok ok${NORMAL}, ${FAILED}$failed failed${NORMAL}"

exit $failed
