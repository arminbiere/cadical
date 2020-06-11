#!/bin/sh

#--------------------------------------------------------------------------#

die () {
  cecho "${HIDE}test/icnf/run.sh:${NORMAL} ${BAD}error:${NORMAL} $*"
  exit 1
}

msg () {
  cecho "${HIDE}test/icnf/run.sh:${NORMAL} $*"
}

for dir in . .. ../..
do
  [ -f $dir/scripts/colors.sh ] || continue
  . $dir/scripts/colors.sh || exit 1
  break
done

#--------------------------------------------------------------------------#

[ -d ../test -a -d ../test/icnf ] || \
die "needs to be called from a top-level sub-directory of CaDiCaL"

[ x"$CADICALBUILD" = x ] && CADICALBUILD="../build"

[ -x "$CADICALBUILD/cadical" ] || \
  die "can not find '$CADICALBUILD/cadical' (run 'make' first)"

cecho -n "$HILITE"
cecho "---------------------------------------------------------"
cecho "ICNF testing in '$CADICALBUILD'" 
cecho "---------------------------------------------------------"
cecho -n "$NORMAL"

make -C $CADICALBUILD
res=$?
[ $res = 0 ] || exit $res

#--------------------------------------------------------------------------#

solver="$CADICALBUILD/cadical"

#--------------------------------------------------------------------------#

ok=0
failed=0

run () {
  msg "running ICNF tests ${HILITE}'$1'${NORMAL}"
  prefix=$CADICALBUILD/test-icnf
  icnf=../test/icnf/$1.icnf
  log=$prefix-$1.log
  err=$prefix-$1.err
  opts="$icnf --check"
  opts="$icnf"
  cecho "$solver \\"
  cecho "$opts"
  cecho -n "# $2 ..."
  "$solver" $opts 1>$log 2>$err
  res=$?
  if [ ! $res = $2 ] 
  then
    cecho " ${BAD}FAILED${NORMAL} (actual exit code $res)"
    failed=`expr $failed + 1`
  else
    cecho " ${GOOD}ok${NORMAL} (exit code '$res' as expected)"
    ok=`expr $ok + 1`
  fi
}

run empty 10
run false 20
run unit1 20
run unit2 10
run two1 20
run two2 10

#--------------------------------------------------------------------------#

[ $ok -gt 0 ] && OK="$GOOD"
[ $failed -gt 0 ] && FAILED="$BAD"

msg "${HILITE}ICNF testing results:${NORMAL} ${OK}$ok ok${NORMAL}, ${FAILED}$failed failed${NORMAL}"

exit $failed
