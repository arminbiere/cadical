#!/bin/sh

#--------------------------------------------------------------------------#

die () {
  cecho "${HIDE}test/usage/run.sh:${NORMAL} ${BAD}error:${NORMAL} $*"
  exit 1
}

msg () {
  cecho "${HIDE}test/usage/run.sh:${NORMAL} $*"
}

for dir in . .. ../..
do
  [ -f $dir/scripts/colors.sh ] || continue
  . $dir/scripts/colors.sh || exit 1
  break
done

#--------------------------------------------------------------------------#

[ -d ../test -a -d ../test/cnf ] || \
die "needs to be called from a top-level sub-directory of CaDiCaL"

[ x"$CADICALBUILD" = x ] && CADICALBUILD="../build"

[ -x "$CADICALBUILD/cadical" ] || \
  die "can not find '$CADICALBUILD/cadical' (run 'make' first)"

cecho -n "$HILITE"
cecho "---------------------------------------------------------"
cecho "usage testing in '$CADICALBUILD'" 
cecho "---------------------------------------------------------"
cecho -n "$NORMAL"

make -C $CADICALBUILD
res=$?
[ $res = 0 ] || exit $res

#--------------------------------------------------------------------------#

solver="$CADICALBUILD/cadical"

#--------------------------------------------------------------------------#

cecho "starting test run `pwd`"

ok=0
failed=0

run () {
  expected="$1"
  options=`echo "$*"|sed -e 's,[^ ]*,,'`
  name=`echo "@-$options"|sed -e 's,\.\./test/.*/,,g' -e 's,\.cnf\>,,g' -e 's,@,,' -e 's,[ \./],-,g' -e 's,--*,-,g'`
  msg "running usage test ${HILITE}'test-usage$name'${NORMAL}"
  buildprefix="$CADICALBUILD/test-usage$name"
  log="$buildprefix.log"
  err="$buildprefix.err"
  cmd="$solver $options"
  cecho -n "$cmd"
  $cmd 1>$log 2>$err
  res=$?
  if [ $res = $expected ]
  then
    cecho " # ${GOOD}ok${NORMAL} (expected exit code '$res')"
    ok=`expr $ok + 1`
  else
    cecho " # ${BAD}FAILED${NORMAL} (unexpected exit code '$res')"
    failed=`expr $failed + 1`
  fi
}

run 0 -h
run 0 --help
run 0 --version
run 0 --build
run 0 --copyright

run 10 ../test/cnf/empty.cnf
run 20 ../test/cnf/false.cnf

if [ x"`$solver --build 2>/dev/null|grep QUIET`" = x ]
then
  run 10 -n ../test/cnf/empty.cnf
  run 10 -v ../test/cnf/empty.cnf
  run 10 -v -v ../test/cnf/empty.cnf
  run 10 -v -v -v ../test/cnf/empty.cnf
  run 10 -q ../test/cnf/empty.cnf
fi

run 1 ../test/usage/missing-clause.cnf
run 1 ../test/usage/variable-too-large.cnf
run 1 --strict relaxed-header.cnf

for option in "-f" "--force" "--force=1" "--force=true"
do
  run 10 $option ../test/usage/missing-clause.cnf
  run 10 $option ../test/usage/variable-too-large.cnf
done

run 20 ../test/usage/relaxed-header.cnf

# TODO:  still need to add test cases for these:

for option in -O1 -O2 -O3
do
  run 10 $option ../test/cnf/prime2209.cnf
done

for option in -L1 -L2 -L10
do
  run 10 $option ../test/cnf/prime9.cnf
done

for option in -P1 -P2 -P16 -P128 -P1024
do
  run 20 $option ../test/cnf/add16.cnf
done

# run 0 -t
# run 0 -O
# run 0 -c 0
# run 0 -c 1
# run 0 -c 2
# run 0 -d 0
# run 0 -d 1
# run 0 -d 2

# run 0 --colors # TODO all versions ....
# run 0 --no-colors # TODO all versions ....
# run 0 --no-leak # not needed

#--------------------------------------------------------------------------#

# not needed since tested in '../cnf'

# run 0 -o # working version not needed since testet in CNF tests
# run 0 -e # working version not needed since testet in CNF tests
# run 0 -s # working version not needed since tested in CNF tests

#--------------------------------------------------------------------------#

[ $ok -gt 0 ] && OK="$GOOD"
[ $failed -gt 0 ] && FAILED="$BAD"

msg "${HILITE}usage testing results:${NORMAL} ${OK}$ok ok${NORMAL}, ${FAILED}$failed failed${NORMAL}"

exit $failed
