#!/bin/sh

cd `dirname $0`

die () {
  echo "*** run-api-tests.sh: $*" 1>&2
  exit 1
}

msg () {
  echo "[run-api-tests.sh] $*"
}

[ x"$CADICAL" = x ] && CADICAL=`pwd`/../build

[ -f "$CADICAL/libcadical.a" ] || die "can not find '$CADICAL/libcadical.a"
[ -f "$CADICAL/makefile" ] || die "can not find '$CADICAL/makefile"

msg "API testing '$CADICAL/libcadical.a'" 

CXX="`grep '^CXX=' $CADICAL/makefile|sed -e 's,CXX=,,'`"

msg "using CXX=$CXX"

run () {
  msg "compiling and executing $1"
  set -x
  $CXX -g api/$1.cpp -o api/$1.exe -L$CADICAL -lcadical || exit 1
  api/$1.exe > api/$1.log 2> api/$1.err || exit 1
  set +x
}

crun () {
  msg "compiling and executing $1"
  set -x
  cc -c -g api/$1.c -o api/$1.o || exit 1
  $CXX -g api/$1.o -o api/$1.exe -L$CADICAL -lcadical || exit 1
  api/$1.exe > api/$1.log 2> api/$1.err || exit 1
  set +x
}


run newdelete
run unit
run morenmore

crun ctest
